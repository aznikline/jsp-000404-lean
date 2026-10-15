import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1441 | h1441
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1442 | h1442
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1443 | h1443
      · linarith only [h0, h1443, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1445 | h1445
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1446 | h1446
          · linarith only [h0, h1441, h1446, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1448 | h1448
            · linarith only [h0, h1441, h1445, h1448, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1450 | h1450
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                · linarith only [h1448, h1451, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h0, h1450, h1451, h3, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1441, h1443, h1450, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1455 | h1455
          · linarith only [h0, h1442, h1445, h1455, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1457 | h1457
            · linarith only [h0, h1442, h1457, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1459 | h1459
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1460 | h1460
                · linarith only [h1457, h1460, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h1460, h2, h3, hc45, hlam, hphi, u4ehi1]
              · linarith only [h1441, h1443, h1459, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1464 | h1464
      · linarith only [h0, h1464, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
        · linarith only [h1441, h1442, h1466, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
          · linarith only [h1441, h1442, h1468, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
            · linarith only [h1470, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1472 | h1472
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
                · linarith only [h1470, h1473, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h0, h1472, h1473, h3, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1441, h1442, h1472, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1477 | h1477
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1478 | h1478
      · linarith only [h0, h1478, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1480 | h1480
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1481 | h1481
          · linarith only [h1, h1481, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1483 | h1483
            · linarith only [h1, h1441, h1477, h1483, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1485 | h1485
              · linarith only [h1441, h1477, h1485, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1487 | h1487
                · linarith only [h1483, h1487, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h0, h1477, h1487, h3, hc45, hlam, hphi, u4ehi2]
        · linarith only [h1441, h1477, h1480, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1491 | h1491
      · linarith only [h0, h1491, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1493 | h1493
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1494 | h1494
          · linarith only [h1, h1494, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1496 | h1496
            · linarith only [h1, h1493, h1496, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
              · linarith only [h0, h1441, h1498, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1500 | h1500
                · linarith only [h1496, h1500, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h1, h1493, h1500, h3, hc45, hlam, hphi, u4ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1503 | h1503
          · linarith only [h1493, h1503, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1505 | h1505
            · linarith only [h1505, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1507 | h1507
              · linarith only [h0, h1441, h1507, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1509 | h1509
                · linarith only [h1505, h1509, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h1509, h2, h3, hc45, hlam, hphi, u4ehi1]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0 m hb0 hb4 h0 h1 h2 h3
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x1 m hb0 hb4 h0 h1 h2 h3

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1512 | h1512
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1513 | h1513
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1514 | h1514
      · linarith only [h0, h1514, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1516 | h1516
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1517 | h1517
          · linarith only [h0, h1513, h1517, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1519 | h1519
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1520 | h1520
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1521 | h1521
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1522 | h1522
                  · rcases h0bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1519, h2, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h2, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h0, hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1519, hc02, hc35, hlam, hphi, ht0b, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1514, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1514, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1513, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1517, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1512, h1522, hc03, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u4ehi4]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1517, hc02, hc34, hlam, hphi, ht23, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1517, hc03, hc34, hlam, hphi, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1512, h1517, h1522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1523_1, u4ehi4]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1512, hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1516, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1519, hlam, p1523_0]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [h1520, hlam, p1523_1]
                    · have p1523_0 := h1523c.1
                      have p1523_1 := h1523c.2.1
                      have p1523_2 := h1523c.2.2.1
                      have p1523_3 := h1523c.2.2.2
                      linarith only [hlam, p1523_0]
                  · linarith only [h0, h1519, h1520, h1521, h1522, h2, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h1513, h1514, h1521, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1513, h1519, h1520, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1552 | h1552
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1554 | h1554
                  · rcases h0bigk with h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1516, h1519, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h2, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1519, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h0, hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1514, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1514, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1514, h1519, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1513, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1517, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1519, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h0, h1553, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1514, hc02, hc24, hlam, hphi, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1517, hc13, hc34, hlam, hphi, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1517, h1519, hc13, hc34, hlam, hphi, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1512, hlam, p1555_0]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1516, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1, h1512, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [h1552, hlam, p1555_1]
                    · have p1555_0 := h1555c.1
                      have p1555_1 := h1555c.2.1
                      have p1555_2 := h1555c.2.2.1
                      have p1555_3 := h1555c.2.2.2
                      linarith only [hlam, p1555_0]
                  · linarith only [h0, h1553, h1554, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1513, h1514, h1553, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1516, h1552, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1584 | h1584
          · linarith only [h1, h1584, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1586 | h1586
            · linarith only [h1513, h1516, h1586, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1588 | h1588
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1589 | h1589
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1590 | h1590
                  · rcases h0bigk with h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h2, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h0, hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1, h1516, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1514, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1516, hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1513, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1584, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1586, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1512, hc04, hc15, hlam, hphi, ht0b, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1514, hc02, hc24, hlam, hphi, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1, h1584, hc13, hc34, hlam, hphi, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h0, h1516, h1584, h1589, hc23, hc34, hlam, hphi, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1512, hlam, p1591_0]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h0, h1589, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1, h1512, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [h1588, hlam, p1591_1]
                    · have p1591_0 := h1591c.1
                      have p1591_1 := h1591c.2.1
                      have p1591_2 := h1591c.2.2.1
                      have p1591_3 := h1591c.2.2.2
                      linarith only [hlam, p1591_0]
                  · linarith only [h0, h1589, h1590, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1513, h1514, h1589, hc12, hc24, hlam, hphi]
              · linarith only [h1512, h1588, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1620 | h1620
      · linarith only [h1, h1513, h1620, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1622 | h1622
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1623 | h1623
          · linarith only [h1, h1623, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1625 | h1625
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1627 | h1627
                · linarith only [h0, h1513, h1627, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1629 | h1629
                  · rcases h0bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1622, h1629, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1513, h1622, h1629, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h2, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1629, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h0, hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1513, hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1620, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1629, hc02, hlam, hphi, ht0b, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1623, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1623, h1629, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1620, hc01, hc24, hlam, hphi, ht12, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1620, h1622, h1629, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1623, hc03, hc34, hlam, hphi, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, h1623, h1629, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1630_1, u4ehi4]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1512, hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1622, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1625, hlam, p1630_0]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [h1626, hlam, p1630_1]
                    · have p1630_0 := h1630c.1
                      have p1630_1 := h1630c.2.1
                      have p1630_2 := h1630c.2.2.1
                      have p1630_3 := h1630c.2.2.2
                      linarith only [hlam, p1630_0]
                  · linarith only [h0, h1629, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1, h1513, h1622, h1626, h2, hlam]
            · linarith only [h1513, h1622, h1625, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1659 | h1659
          · linarith only [h1, h1659, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1661 | h1661
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1662 | h1662
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1663 | h1663
                · linarith only [h0, h1513, h1663, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1665 | h1665
                  · rcases h0bigk with h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h2, hlam, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1512, h1665, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1666_1, u4ehi4]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1513, hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1620, hlam, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1622, hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1, hlam, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1659, hlam, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1512, h1659, h1665, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1666_1, u4ehi4]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, h1620, hc12, hc24, hlam, hphi, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1659, hc03, hc34, hlam, hphi, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1512, h1659, h1665, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1666_1, u4ehi4]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1512, hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h0, h1, h1661, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1661, hlam, p1666_0]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [h1662, hlam, p1666_1]
                    · have p1666_0 := h1666c.1
                      have p1666_1 := h1666c.2.1
                      have p1666_2 := h1666c.2.2.1
                      have p1666_3 := h1666c.2.2.2
                      linarith only [hlam, p1666_0]
                  · linarith only [h0, h1665, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1, h1661, h1662, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1694 | h1694
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1695 | h1695
                · linarith only [h0, h1513, h1695, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1697 | h1697
                  · rcases h0bigk with h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h0, h1513, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h2, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h0, hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1513, hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1620, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1622, hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h0, h1661, hc12, hc35, hlam, hphi, ht23, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1659, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1661, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h2, hc01, hc14, hlam, hphi, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h0, h1620, hc12, hc24, hlam, hphi, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1659, hc03, hc34, hlam, hphi, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1, h1659, h1661, h1695, hc12, hc34, hlam, hphi, ht23, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1512, hlam, p1698_0]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h0, h1512, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1, h1512, h1695, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [h1694, hlam, p1698_1]
                    · have p1698_0 := h1698c.1
                      have p1698_1 := h1698c.2.1
                      have p1698_2 := h1698c.2.2.1
                      have p1698_3 := h1698c.2.2.2
                      linarith only [hlam, p1698_0]
                  · linarith only [h0, h1697, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1512, h1694, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1726 | h1726
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1727 | h1727
      · linarith only [h0, h1727, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1729 | h1729
        · linarith only [h0, h1512, h1729, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1731 | h1731
          · linarith only [h0, h1726, h1731, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1733 | h1733
            · linarith only [h0, h1512, h1726, h1733, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1735 | h1735
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1736 | h1736
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1737 | h1737
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
                      linarith only [h1512, h1737, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1512, h1737, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h2, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1512, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1, h1727, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1727, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1729, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1726, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1731, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1733, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1736, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1727, hc02, hc24, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1, h1731, hc13, hc34, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1512, h1731, h1736, hc23, hc34, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1736, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1733, h1736, hc23, hc35, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1, h1733, hc13, hc35, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1735, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                  · linarith only [h0, h1731, h1735, h1736, h1737, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1726, h1727, h1736, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1766 | h1766
                · linarith only [h0, h1735, h1766, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1726, h1735, h1766, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1769 | h1769
      · linarith only [h1, h1726, h1769, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1771 | h1771
        · linarith only [h1, h1512, h1726, h1771, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1773 | h1773
          · linarith only [h1, h1773, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1775 | h1775
            · linarith only [h1, h1512, h1775, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1777 | h1777
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1778 | h1778
                · linarith only [h0, h1726, h1778, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1780 | h1780
                  · rcases h0bigk with h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1512, h1780, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1512, h1780, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h2, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1512, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1726, hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1769, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1771, hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1775, hc12, hc35, hlam, hphi, ht23, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1773, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1775, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1769, hc01, hc24, hlam, hphi, ht12, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1769, hc12, hc24, hlam, hphi, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1773, hc03, hc34, hlam, hphi, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [hlam, p1781_0]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1512, h1773, hc12, hc34, hlam, hphi, ht23, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1771, hc12, hc25, hlam, hphi, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h0, h1726, h1775, hc12, hc35, hlam, hphi, ht23, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [h1777, hlam, p1781_1]
                    · have p1781_0 := h1781c.1
                      have p1781_1 := h1781c.2.1
                      have p1781_2 := h1781c.2.2.1
                      have p1781_3 := h1781c.2.2.2
                      linarith only [hlam, p1781_0]
                  · linarith only [h1777, h1780, h2, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1808 | h1808
                · linarith only [h0, h1726, h1808, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1810 | h1810
                  · rcases h0bigk with h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1726, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h2, hlam, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1512, hlam, p1811_1]
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
                      linarith only [h1726, hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1769, hlam, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1771, hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1, hlam, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1773, hlam, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1775, hlam, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1777, h1810, hc01, hc14, hlam, hphi, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1777, h1810, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1777, h1810, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1777, hlam, p1811_0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1777, h1810, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1777, h1810, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h0, h1726, h1777, h1810, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1811_1]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [h1777, h1810, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1811_1, u4ehi0]
                    · have p1811_0 := h1811c.1
                      have p1811_1 := h1811c.2.1
                      have p1811_2 := h1811c.2.2.1
                      have p1811_3 := h1811c.2.2.2
                      linarith only [hlam, p1811_0]
                  · linarith only [h1, h1808, h1810, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0 m hb0 hb4 h0 h1 h2
  · exact r1l7_20_14_H_I_L_R_x0_x0_x1 m hb0 hb4 h0 h1 h2

end R2N4
