import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1424 | h1424
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1425 | h1425
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1426 | h1426
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
        · linarith only [h1427, h4, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1434 | h1434
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1435 | h1435
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h0, h1429, h1436, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h1424, h1426, h1434, h1436, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h0, h1, h1430, h1432, h1435, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1425, h1434, h4, hlam]
                  · linarith only [h1424, h1426, h1431, h1433, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1427, h1430, h1432, hlam]
              · linarith only [h1425, h1427, h1429, h1431, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1446 | h1446
                  · linarith only [h1429, h1430, h1446, hlam]
                  · linarith only [h1424, h1426, h1446, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                  · linarith only [h1427, h1429, h1445, h1449, hlam]
                  · linarith only [h1424, h1426, h1449, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1425, h1427, h1429, h1444, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h1424, h1429, h4, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
        · linarith only [h1454, h4, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1456 | h1456
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1457 | h1457
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1458 | h1458
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1459 | h1459
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1460 | h1460
                  · linarith only [h1426, h1460, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1462 | h1462
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1463 | h1463
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1464 | h1464
                        · linarith only [h0, h1426, h1456, h1464, h2, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1466 | h1466
                          · linarith only [h1426, h1456, h1462, h1466, h2, hlam]
                          · rcases h2bigk with h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c | h1468c
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h4, hc12, hlam, hphi, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h4, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1462, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1462, h1464, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h0, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1454, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h0, h1462, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h0, h1462, h1464, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hc02, hlam, hphi, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hc12, hlam, hphi, p1468_1, u2elo2]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              rcases p1468_3 (m.d 0 2) (by simp) with h1482 | h1482
                              · linarith only [h1482, h4, hlam]
                              · linarith only [h1424, h1482, hlam]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              rcases p1468_3 (m.d 0 2) (by simp) with h1485 | h1485
                              · linarith only [h1485, h4, hlam]
                              · linarith only [h0, h1457, h1485, hlam]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1424, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1456, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1462, hlam, p1468_1]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1464, hlam, p1468_1]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h0, h1457, hlam, p1468_1]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1457, hlam, p1468_0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h1463, hlam, p1468_1]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [h0, h1457, h1462, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1468_1, u2elo0]
                            · have p1468_0 := h1468c.1
                              have p1468_1 := h1468c.2.1
                              have p1468_2 := h1468c.2.2.1
                              have p1468_3 := h1468c.2.2.2
                              linarith only [hlam, p1468_0]
                      · linarith only [h0, h1457, h1459, h1463, h3, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1425, h1456, h1462, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1454, h1457, h1459, hlam]
              · linarith only [h1425, h1454, h1456, h1458, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                  · linarith only [h1426, h1504, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1507 | h1507
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1508 | h1508
                        · linarith only [h1426, h1456, h1457, h1508, h3, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1510 | h1510
                          · linarith only [h1456, h1457, h1506, h1508, h1510, hlam]
                          · rcases h2bigk with h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1456, h1506, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h4, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1506, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1456, h1457, h1506, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h0, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1454, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1457, h1506, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo4]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1457, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hc02, hlam, hphi, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hc12, hlam, hphi, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              rcases p1512_3 (m.d 0 2) (by simp) with h1526 | h1526
                              · linarith only [h1526, h4, hlam]
                              · linarith only [h1424, h1526, hlam]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1456, h1457, h1506, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo2]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1424, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1456, hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1506, hlam, p1512_1]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hlam, p1512_0]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1508, hlam, p1512_1]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hc02, hlam, hphi, p1512_1, u2elo4]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1456, h1506, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1512_1, u2elo4]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [h1507, hlam, p1512_1]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              rcases p1512_3 (m.d 0 2) (by simp) with h1538 | h1538
                              · linarith only [h1456, h1457, h1506, h1538, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                              · linarith only [h1424, h1538, hlam]
                            · have p1512_0 := h1512c.1
                              have p1512_1 := h1512c.2.1
                              have p1512_2 := h1512c.2.2.1
                              have p1512_3 := h1512c.2.2.2
                              linarith only [hlam, p1512_0]
                      · linarith only [h0, h1456, h1503, h1506, h1507, h4, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1425, h1456, h1506, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1544 | h1544
                  · linarith only [h1426, h1544, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1547 | h1547
                      · linarith only [h1454, h1456, h1503, h1546, h1547, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1549 | h1549
                        · linarith only [h0, h1426, h1456, h1549, h2, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1551 | h1551
                          · linarith only [h1546, h1547, h1549, h1551, h4, hc02, hlam, hphi, u2elo3]
                          · linarith only [h0, h1456, h1546, h1547, h1551, h4, hc34, hc45, hlam, hphi]
                    · linarith only [h1425, h1546, h4, hlam]
              · linarith only [h1424, h1425, h1454, h1456, h1502, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h1424, h1456, h4, hc12, hlam, hphi, u2elo2]
    · linarith only [h1424, h1425, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1559 | h1559
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
        · linarith only [h1560, h4, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1562 | h1562
          · linarith only [h0, h1424, h1562, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1564 | h1564
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1566 | h1566
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
                              linarith only [h1424, h1564, h1568, h1569, h1571, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h4, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1424, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1569, h1571, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1560, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1562, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, h1569, h1571, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hc02, hlam, hphi, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hc12, hlam, hphi, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1424, hc02, hlam, hphi, p1572_1, u2elo2]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              rcases p1572_3 (m.d 0 2) (by simp) with h1587 | h1587
                              · linarith only [h1587, h4, hlam]
                              · linarith only [h0, h1564, h1587, hlam]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, h1564, h1569, h1571, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1572_1, u2elo3]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1564, h1569, h1571, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1572_1, u2elo3]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1568, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              rcases p1572_3 (m.d 0 2) (by simp) with h1594 | h1594
                              · linarith only [h1424, h1594, hlam]
                              · linarith only [h0, h1564, h1594, hlam]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, h1564, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1564, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1569, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1570, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                          · linarith only [h0, h1564, h1570, h1571, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h0, h1424, h1564, h1567, h1570, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1424, h1564, h1566, h1568, h1569, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1558, h1568, h4, hlam]
                  · linarith only [h1558, h1559, h1562, h1564, h1567, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1560, h1564, h1566, hlam]
              · linarith only [h1558, h1560, h1565, h4, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1609 | h1609
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1610 | h1610
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1611 | h1611
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1613 | h1613
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1614 | h1614
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1615 | h1615
                          · rcases h2bigk with h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hc12, hlam, hphi, p1616_1, u2elo0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h4, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1424, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1424, h1564, h1612, hc12, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h0, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1560, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1562, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1564, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hc02, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hc12, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h0, h1424, hc12, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1564, hc12, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1616_1, u2elo3]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hc12, hlam, hphi, p1616_1, u2elo3]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1612, hlam, p1616_1]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1564, h1612, hc12, hlam, hphi, p1616_1, u2elo2]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1616_1, u2elo4]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hc12, hlam, hphi, p1616_1, u2elo4]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1613, hlam, p1616_1]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [h1614, hlam, p1616_0]
                            · have p1616_0 := h1616c.1
                              have p1616_1 := h1616c.2.1
                              have p1616_2 := h1616c.2.2.1
                              have p1616_3 := h1616c.2.2.2
                              linarith only [hlam, p1616_0]
                          · rcases h2bigk with h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hc12, hlam, hphi, p1642_1, u2elo0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h4, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1424, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1424, h1612, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h0, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1560, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1562, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1564, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hc02, hlam, hphi, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hc12, hlam, hphi, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h0, h1424, hc12, hlam, hphi, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1564, hc12, hlam, hphi, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1642_1, u2elo3]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hc12, hlam, hphi, p1642_1, u2elo3]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1612, hlam, p1642_1]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1564, h1612, hc12, hlam, hphi, p1642_1, u2elo2]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1642_1, u2elo4]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hc12, hlam, hphi, p1642_1, u2elo4]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1613, hlam, p1642_1]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [h1614, hlam, p1642_0]
                            · have p1642_0 := h1642c.1
                              have p1642_1 := h1642c.2.1
                              have p1642_2 := h1642c.2.2.1
                              have p1642_3 := h1642c.2.2.2
                              linarith only [hlam, p1642_0]
                        · linarith only [h0, h1424, h1558, h1559, h1611, h1614, h3, h4, hc12, hlam, hphi, u2elo2]
                      · linarith only [h1, h1610, h1613, h4, hlam]
                    · linarith only [h1558, h1612, h4, hlam]
                  · linarith only [h1558, h1559, h1562, h1611, h4, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1672 | h1672
                  · linarith only [h1609, h1610, h1672, hlam]
                  · linarith only [h1558, h1559, h1562, h1672, h4, hc12, hlam, hphi, u2elo2]
              · linarith only [h1558, h1560, h1609, h4, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1676 | h1676
        · linarith only [h0, h1676, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
          · linarith only [h0, h1424, h1678, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1680 | h1680
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1681 | h1681
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1682 | h1682
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1683 | h1683
                  · linarith only [h1559, h1683, h2, hlam]
                  · linarith only [h1678, h1680, h1683, hlam]
                · linarith only [h1676, h1680, h1682, hlam]
              · linarith only [h1558, h1676, h1680, h1681, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1688 | h1688
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1689 | h1689
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1690 | h1690
                  · linarith only [h1559, h1690, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1692 | h1692
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1693 | h1693
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1694 | h1694
                        · linarith only [h0, h1424, h1559, h1694, hc12, hlam, hphi, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1696 | h1696
                          · linarith only [h0, h1424, h1694, h1696, hc12, hc34, hlam, hphi, ht23]
                          · rcases h2bigk with h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1424, hc12, hlam, hphi, p1698_1, u2elo3]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h4, hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1424, hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1424, h1694, hlam, p1698_1]
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
                              linarith only [h1676, hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1678, hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1680, hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hc02, hlam, hphi, p1698_1, u2elo2]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hc12, hlam, hphi, p1698_1, u2elo2]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h0, h1424, hc12, hlam, hphi, p1698_1, u2elo2]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1680, hc12, hlam, hphi, p1698_1, u2elo2]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1698_1, u2elo3]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hc12, hlam, hphi, p1698_1, u2elo3]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1692, hlam, p1698_1]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hlam, p1698_0]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1694, hlam, p1698_1]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1698_1, u2elo4]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hc12, hlam, hphi, p1698_1, u2elo4]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h1693, hlam, p1698_1]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [h0, h1424, h1693, hc12, hlam, hphi, p1698_1, u2elo2]
                            · have p1698_0 := h1698c.1
                              have p1698_1 := h1698c.2.1
                              have p1698_2 := h1698c.2.2.1
                              have p1698_3 := h1698c.2.2.2
                              linarith only [hlam, p1698_0]
                      · linarith only [h1, h1689, h1693, h4, hlam]
                    · linarith only [h0, h1424, h1688, h1692, h2, h4, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1726 | h1726
                  · linarith only [h1559, h1726, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1728 | h1728
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1729 | h1729
                      · linarith only [h1688, h1689, h1729, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1731 | h1731
                        · linarith only [h0, h1424, h1559, h1728, h1729, h1731, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1733 | h1733
                          · linarith only [h1688, h1689, h1731, h1733, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h2bigk with h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1424, hc12, hlam, hphi, p1735_1, u2elo3]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h4, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1424, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1424, h1680, h1728, h1729, h1733, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h0, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1676, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1678, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1680, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1729, h1733, hc02, hc45, hlam, hphi, ht23, ht34, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1729, h1733, hc12, hc45, hlam, hphi, ht23, ht34, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1729, h1733, hc24, hc45, hlam, hphi, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1729, hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1735_1, u2elo3]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hc12, hlam, hphi, p1735_1, u2elo3]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1728, hlam, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hlam, p1735_0]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h1731, hlam, p1735_1]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1735_1, u2elo4]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hc12, hlam, hphi, p1735_1, u2elo4]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1735_1, u2elo4]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [h0, h1424, hc12, hlam, hphi, p1735_1, u2elo4]
                            · have p1735_0 := h1735c.1
                              have p1735_1 := h1735c.2.1
                              have p1735_2 := h1735c.2.2.1
                              have p1735_3 := h1735c.2.2.2
                              linarith only [hlam, p1735_0]
                    · linarith only [h0, h1424, h1688, h1728, h2, h4, hc12, hlam, hphi, u2elo3]
              · linarith only [h1558, h1676, h1688, h4, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1763 | h1763
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
        · linarith only [h0, h1764, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1766 | h1766
          · linarith only [h0, h1424, h1766, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1768 | h1768
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1769 | h1769
              · linarith only [h1, h1558, h1769, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1771 | h1771
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1772 | h1772
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1773 | h1773
                    · linarith only [h1558, h1773, h4, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1775 | h1775
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1776 | h1776
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1777 | h1777
                          · rcases h2bigk with h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1768, h1773, h1775, h1777, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h4, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1424, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1773, h1775, h1777, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h0, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1764, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1766, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h0, h1773, h1775, h1777, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1773, hc02, hc34, hlam, hphi, ht23, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1773, hc12, hc34, hlam, hphi, ht23, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1773, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              rcases p1778_3 (m.d 0 2) (by simp) with h1793 | h1793
                              · linarith only [h1793, h4, hlam]
                              · linarith only [h0, h1768, h1793, hlam]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h0, h1768, h1775, h1777, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1778_1, u2elo3]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1768, h1775, h1777, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1778_1, u2elo3]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h0, h1768, h1775, h1777, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1778_1, u2elo3]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              rcases p1778_3 (m.d 0 2) (by simp) with h1800 | h1800
                              · linarith only [h1424, h1800, hlam]
                              · linarith only [h0, h1768, h1800, hlam]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h0, h1768, hlam, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1768, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1775, hlam, p1778_1]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [h1776, hlam, p1778_0]
                            · have p1778_0 := h1778c.1
                              have p1778_1 := h1778c.2.1
                              have p1778_2 := h1778c.2.2.1
                              have p1778_3 := h1778c.2.2.2
                              linarith only [hlam, p1778_0]
                          · linarith only [h0, h1558, h1763, h1768, h1777, h4, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1424, h1763, h1772, h1776, h3, hlam]
                      · linarith only [h0, h1, h1768, h1771, h1775, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1424, h1763, h1766, h1768, h1772, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h1764, h1768, h1771, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1813 | h1813
              · linarith only [h1, h1558, h1813, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1815 | h1815
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1816 | h1816
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1817 | h1817
                    · linarith only [h1, h1558, h1768, h1815, h1817, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1819 | h1819
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1820 | h1820
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1821 | h1821
                          · rcases h2bigk with h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hc12, hlam, hphi, p1822_1, u2elo0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h4, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1424, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1768, h1817, h4, hc12, hc34, hlam, hphi, ht23, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h0, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1764, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1766, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1768, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1817, hc02, hc34, hlam, hphi, ht23, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1817, hc12, hc34, hlam, hphi, ht23, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1817, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1768, h1817, hc12, hc34, hlam, hphi, ht23, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1822_1, u2elo3]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hc12, hlam, hphi, p1822_1, u2elo3]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1822_1, u2elo3]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1768, hc12, hlam, hphi, p1822_1, u2elo3]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1822_1, u2elo4]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hc12, hlam, hphi, p1822_1, u2elo4]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1819, hlam, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1820, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                          · linarith only [h1, h1558, h1763, h1815, h1821, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1424, h1763, h1816, h1820, h3, hlam]
                      · linarith only [h0, h1, h1815, h1819, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1424, h1763, h1766, h1816, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1852 | h1852
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1853 | h1853
                    · linarith only [h0, h1558, h1853, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1855 | h1855
                      · linarith only [h1815, h1853, h1855, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1857 | h1857
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1858 | h1858
                          · rcases h2bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hc12, hlam, hphi, p1859_1, u2elo0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h4, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1424, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1855, h4, hlam, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1764, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1766, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1768, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1855, h1857, hc02, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1855, h1857, hc12, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1853, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1855, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hc12, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1768, hc12, hlam, hphi, p1859_1, u2elo3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p1859_1, u2elo4]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hc12, hlam, hphi, p1859_1, u2elo4]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1859_1, u2elo4]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1857, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                          · linarith only [h0, h1424, h1558, h1852, h1858, h2, h4, hc12, hlam, hphi, u2elo3]
                        · linarith only [h1424, h1763, h1852, h1857, h3, hlam]
                  · linarith only [h1424, h1763, h1766, h1852, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1888 | h1888
        · linarith only [h0, h1888, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1890 | h1890
          · linarith only [h0, h1424, h1890, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
              · linarith only [h1, h1558, h1893, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1895 | h1895
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1896 | h1896
                  · linarith only [h1763, h1896, h2, hlam]
                  · linarith only [h1890, h1892, h1896, hlam]
                · linarith only [h1888, h1892, h1895, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1900 | h1900
              · linarith only [h1, h1558, h1900, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1902 | h1902
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1903 | h1903
                  · linarith only [h1763, h1903, h2, hlam]
                  · linarith only [h1900, h1902, h1903, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1906 | h1906
                  · linarith only [h1763, h1906, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1908 | h1908
                    · linarith only [h0, h1558, h1908, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1910 | h1910
                      · linarith only [h1888, h1902, h1908, h1910, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1912 | h1912
                        · linarith only [h0, h1424, h1763, h1912, hc12, hlam, hphi, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1914 | h1914
                          · linarith only [h0, h1908, h1912, h1914, h4, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1908, h1914, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0 m hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x1 m hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1917 | h1917
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1918 | h1918
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1919 | h1919
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1920 | h1920
        · linarith only [h1920, h2, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1922 | h1922
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1923 | h1923
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1924 | h1924
              · linarith only [h0, h1924, h3, hlam]
              · linarith only [h0, h1922, h1924, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h1918, h1922, h1923, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h1917, h1922, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1929 | h1929
        · linarith only [h0, h1918, h1929, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1931 | h1931
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1932 | h1932
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1933 | h1933
              · linarith only [h0, h1933, h3, hlam]
              · linarith only [h0, h1931, h1933, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h0, h1918, h1931, h1932, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h1917, h1931, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1938 | h1938
      · linarith only [h1917, h1918, h1938, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1940 | h1940
        · linarith only [h1940, h2, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1942 | h1942
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1943 | h1943
            · linarith only [h0, h1918, h1943, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1945 | h1945
              · linarith only [h0, h1918, h1945, h3, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h1942, h1943, h1945, h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h1917, h1942, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1949 | h1949
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1950 | h1950
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1951 | h1951
        · linarith only [h0, h1917, h1949, h1951, h3, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1953 | h1953
          · linarith only [h1917, h1953, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1955 | h1955
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1956 | h1956
              · linarith only [h1, h1953, h1956, h3, hlam]
              · linarith only [h1, h1953, h1955, h1956, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
            · linarith only [h1917, h1949, h1955, hc12, hlam, hphi, u2elo2]
      · linarith only [h1917, h1949, h1950, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1961 | h1961
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1962 | h1962
        · linarith only [h1, h1961, h1962, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1964 | h1964
          · linarith only [h0, h1917, h1964, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1966 | h1966
            · linarith only [h0, h1949, h1966, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1968 | h1968
              · linarith only [h0, h1949, h1968, h3, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h1, h1964, h1968, h3, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1971 | h1971
        · linarith only [h1971, h2, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1973 | h1973
          · linarith only [h0, h1917, h1973, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1975 | h1975
            · linarith only [h0, h1949, h1975, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1977 | h1977
              · linarith only [h0, h1, h1917, h1977, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h1, h1973, h1977, h3, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0 m hb2 hb4 h0 h1 h2 h3
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x1 m hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1980 | h1980
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1981 | h1981
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1982 | h1982
      · linarith only [h0, h1982, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1984 | h1984
        · linarith only [h0, h1981, h1984, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1986 | h1986
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1987 | h1987
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1988 | h1988
              · linarith only [h0, h1982, h1988, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1987, h1988, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h1981, h1987, hc12, hlam, hphi, u2elo0]
          · linarith only [h1980, h1986, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1993 | h1993
      · linarith only [h1, h1981, h1993, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1995 | h1995
        · linarith only [h1, h1995, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1997 | h1997
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1998 | h1998
            · linarith only [h0, h1981, h1998, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2000 | h2000
              · linarith only [h0, h1993, h2, h2000, hlam]
              · linarith only [h1, h1998, h2, h2000, hc12, hlam, hphi, u2elo3]
          · linarith only [h1980, h1997, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2004 | h2004
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2005 | h2005
      · linarith only [h0, h2, h2005, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2007 | h2007
        · linarith only [h0, h2, h2004, h2007, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2009 | h2009
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2010 | h2010
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2011 | h2011
              · linarith only [h0, h2, h2005, h2011, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h2, h2010, h2011, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1980, h2004, h2005, h2009, h2010, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2015 | h2015
            · linarith only [h0, h2, h2009, h2015, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2004, h2005, h2015, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2018 | h2018
      · linarith only [h0, h2, h2004, h2018, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2020 | h2020
        · linarith only [h1, h2, h2020, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2022 | h2022
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2023 | h2023
            · linarith only [h2004, h2023, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2025 | h2025
              · linarith only [h1, h2, h2018, h2023, h2025, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h2, h2025, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2028 | h2028
            · linarith only [h0, h2004, h2028, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2030 | h2030
              · linarith only [h1, h2, h2022, h2028, h2030, hc24, hc45, hlam, hphi]
              · linarith only [h1, h2, h2028, h2030, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0 m hb2 hb4 h0 h1 h2
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x1 m hb2 hb4 h0 h1 h2

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2033 | h2033
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2034 | h2034
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2035 | h2035
      · linarith only [h0, h1, h2035, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2037 | h2037
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2038 | h2038
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2039 | h2039
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2040 | h2040
              · linarith only [h0, h1, h2035, h2040, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2040, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
              · linarith only [h0, h1, h2035, h2043, hlam]
              · linarith only [h0, h1, h2043, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h2037, h2038, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2047 | h2047
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2048 | h2048
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2049 | h2049
              · linarith only [h0, h1, h2035, h2049, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2049, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2052 | h2052
              · linarith only [h0, h1, h2035, h2052, hlam]
              · linarith only [h0, h1, h2052, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h2033, h2047, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2056 | h2056
      · linarith only [h0, h1, h2056, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2058 | h2058
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2059 | h2059
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2060 | h2060
            · linarith only [h0, h2034, h2058, h2060, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2062 | h2062
              · linarith only [h0, h1, h2056, h2062, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2062, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h2058, h2059, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2066 | h2066
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2067 | h2067
            · linarith only [h2033, h2034, h2067, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2069 | h2069
              · linarith only [h0, h1, h2056, h2069, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2069, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h2033, h2066, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2073 | h2073
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2074 | h2074
      · linarith only [h0, h1, h2074, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2076 | h2076
        · linarith only [h0, h2033, h2076, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2078 | h2078
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2079 | h2079
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2080 | h2080
              · linarith only [h0, h1, h2074, h2080, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2080, hc12, hlam, hphi, u2elo2]
            · linarith only [h2033, h2073, h2079, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2084 | h2084
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
              · linarith only [h0, h1, h2078, h2085, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h2085, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h2073, h2078, h2084, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2089 | h2089
      · linarith only [h0, h1, h2089, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2091 | h2091
        · linarith only [h0, h2033, h2091, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2093 | h2093
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2094 | h2094
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2095 | h2095
              · linarith only [h0, h1, h2089, h2095, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h2095, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2098 | h2098
              · linarith only [h0, h1, h2089, h2093, h2098, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h0, h1, h2098, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2101 | h2101
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2102 | h2102
              · linarith only [h0, h1, h2093, h2102, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h2102, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2105 | h2105
              · linarith only [h0, h1, h2093, h2105, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h2105, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_14_M_LI_L_I_x0_x0 m hb2 hb4 h0 h1
  · exact r1l7_22_14_M_LI_L_I_x0_x1 m hb2 hb4 h0 h1

end R2N4
