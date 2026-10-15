import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1416 | h1416
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1417 | h1417
    · linarith only [h1417, h3, h4, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1419 | h1419
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1420 | h1420
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1421 | h1421
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1422 | h1422
            · linarith only [h1422, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1424 | h1424
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1425 | h1425
                · linarith only [h1, h1417, h1425, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1427 | h1427
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1428 | h1428
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1429 | h1429
                      · linarith only [h0, h1, h1417, h1421, h1427, h1429, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1431 | h1431
                        · linarith only [h0, h1421, h1431, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h1, h1427, h1431, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h1420, h1422, h1428, h4, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1419, h1427, h3, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h1416, h1421, h1424, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h1421, h3, h4, hc12, hlam, hphi, u2elo3]
        · linarith only [h1419, h1420, h3, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1439 | h1439
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1440 | h1440
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1441 | h1441
            · linarith only [h1441, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1443 | h1443
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1444 | h1444
                · linarith only [h1, h1417, h1444, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1446 | h1446
                  · linarith only [h1, h1419, h1446, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1448 | h1448
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1449 | h1449
                      · linarith only [h0, h1, h1417, h1440, h1449, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1451 | h1451
                        · linarith only [h1, h1419, h1440, h1451, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1453 | h1453
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1454 | h1454
                            · rcases h2bigk with h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1443, h1451, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h4, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1451, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h0, hlam, p1455_1]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1441, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h0, h1451, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h3, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1440, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1449, hlam, p1455_1]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1451, hlam, p1455_1]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hc02, hlam, hphi, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1440, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo3]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                rcases p1455_3 (m.d 0 2) (by simp) with h1473 | h1473
                                · linarith only [h1473, h4, hlam]
                                · linarith only [h1473, h3, hlam]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                rcases p1455_3 (m.d 0 2) (by simp) with h1477 | h1477
                                · linarith only [h1477, h4, hlam]
                                · linarith only [h1416, h1477, hlam]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1416, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1443, hlam, p1455_0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h0, h1443, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1455_1, u2elo0]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [h1453, hlam, p1455_1]
                              · have p1455_0 := h1455c.1
                                have p1455_1 := h1455c.2.1
                                have p1455_2 := h1455c.2.2.1
                                have p1455_3 := h1455c.2.2.2
                                linarith only [hlam, p1455_0]
                            · linarith only [h0, h1443, h1449, h1453, h1454, h4, hlam]
                          · linarith only [h1453, h3, h4, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1416, h1439, h1441, h1448, h4, hc12, hlam, hphi, u2elo3]
              · linarith only [h1416, h1440, h1443, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h1440, h3, h4, hc12, hlam, hphi, u2elo3]
        · linarith only [h1416, h1439, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1491 | h1491
    · linarith only [h1491, h3, h4, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
      · linarith only [h1416, h1493, h3, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1495 | h1495
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1496 | h1496
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1497 | h1497
            · linarith only [h1497, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1499 | h1499
              · linarith only [h0, h1416, h1499, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
                · linarith only [h0, h1491, h1496, h1501, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h1, h1416, h1493, h1503, h3, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1505 | h1505
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
                      · linarith only [h1491, h1506, h3, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1508 | h1508
                        · linarith only [h1416, h1493, h1508, h3, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1510 | h1510
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1511 | h1511
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
                                linarith only [h1416, h1510, hc12, hlam, hphi, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1416, h1510, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h4, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1416, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h0, hlam, p1512_1]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h0, h1416, h1510, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1497, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1499, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h3, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1496, hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1506, hlam, p1512_1]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1508, hlam, p1512_1]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [hc02, hlam, hphi, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                rcases p1512_3 (m.d 0 2) (by simp) with h1530 | h1530
                                · linarith only [h1530, h4, hlam]
                                · linarith only [h1530, h3, hlam]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [hlam, p1512_0]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h0, h1416, h1496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo3]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h0, h1496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo4]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1512_1, u2elo4]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                rcases p1512_3 (m.d 0 2) (by simp) with h1537 | h1537
                                · linarith only [h1416, h1537, hlam]
                                · linarith only [h1537, h3, hlam]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [h1510, hlam, p1512_1]
                              · have p1512_0 := h1512c.1
                                have p1512_1 := h1512c.2.1
                                have p1512_2 := h1512c.2.2.1
                                have p1512_3 := h1512c.2.2.2
                                linarith only [hlam, p1512_0]
                            · linarith only [h0, h1496, h1506, h1511, h4, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1496, h1505, h1510, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1495, h1496, h1497, h1505, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h1416, h1496, h3, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1546 | h1546
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1547 | h1547
            · linarith only [h1547, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1549 | h1549
              · linarith only [h0, h1416, h1549, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1551 | h1551
                · linarith only [h1, h1491, h1551, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1553 | h1553
                  · linarith only [h1, h1493, h1553, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1555 | h1555
                    · linarith only [h0, h1495, h1546, h1547, h1555, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1557 | h1557
                      · linarith only [h0, h1, h1416, h1491, h1546, h1557, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1559 | h1559
                        · linarith only [h1416, h1493, h1559, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1561 | h1561
                          · linarith only [h0, h1495, h1546, h1561, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · linarith only [h0, h1546, h1561, h4, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1546, h3, h4, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1565 | h1565
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1566 | h1566
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1567 | h1567
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1568 | h1568
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1569 | h1569
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
            · linarith only [h1570, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1572 | h1572
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1573 | h1573
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1574 | h1574
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1575 | h1575
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1576 | h1576
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1577 | h1577
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1578 | h1578
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1579 | h1579
                            · linarith only [h0, h1572, h1579, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h1565, h1569, h1577, h1579, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h0, h1568, h1573, h1578, h3, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1567, h1577, h3, hlam]
                      · linarith only [h1565, h1569, h1576, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h1565, h1568, h1569, h1570, h1575, h3, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1567, h1570, h1572, h1574, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1566, h1572, h1573, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1565, h1572, h3, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1589 | h1589
            · linarith only [h1589, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1591 | h1591
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1592 | h1592
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1593 | h1593
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1594 | h1594
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1595 | h1595
                      · linarith only [h0, h1569, h1591, h1595, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1597 | h1597
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1598 | h1598
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1599 | h1599
                            · linarith only [h1565, h1595, h1599, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1601 | h1601
                              · linarith only [h1565, h1569, h1597, h1601, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · rcases h2bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h3, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1597, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1597, h1599, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h0, hlam, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1589, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h0, h1597, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h0, h1597, h1599, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1603_1, u2elo2]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  rcases p1603_3 (m.d 0 2) (by simp) with h1617 | h1617
                                  · linarith only [h1617, h3, hlam]
                                  · linarith only [h1565, h1617, hlam]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  rcases p1603_3 (m.d 0 2) (by simp) with h1620 | h1620
                                  · linarith only [h1620, h3, hlam]
                                  · linarith only [h1566, h1620, hlam]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1565, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1591, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1597, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1599, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1566, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1592, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1598, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h0, h1592, h1597, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                          · linarith only [h1565, h1594, h1597, h1598, h2, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1567, h1597, h3, hlam]
                    · linarith only [h1566, h1568, h1589, h1591, h1594, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1566, h1567, h1569, h1589, h1591, h1593, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1566, h1591, h1592, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1565, h1591, h3, hc12, hlam, hphi, u2elo2]
        · linarith only [h1566, h1568, h3, hlam]
      · linarith only [h1565, h1567, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1641 | h1641
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1642 | h1642
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1643 | h1643
          · linarith only [h1565, h1566, h1643, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1645 | h1645
            · linarith only [h1645, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1647 | h1647
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1648 | h1648
                · linarith only [h0, h1566, h1648, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1650 | h1650
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1651 | h1651
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1652 | h1652
                      · linarith only [h0, h1643, h1647, h1652, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1656 | h1656
                            · linarith only [h1565, h1566, h1652, h1655, h1656, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1658 | h1658
                              · linarith only [h1566, h1654, h1656, h1658, hc02, hlam, hphi, u2elo3]
                              · rcases h2bigk with h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1566, h1647, h1654, h1655, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h3, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1566, h1654, h1655, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1566, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h0, hlam, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1645, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h0, h1566, h1654, h1655, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1648, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 2) (by simp) with h1674 | h1674
                                  · linarith only [h1674, h3, hlam]
                                  · linarith only [h1565, h1674, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h0, h1566, h1647, h1654, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo2]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1565, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1647, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1654, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1656, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h0, h1647, h1654, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo4]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1647, h1654, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1660_1, u2elo4]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1655, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 2) (by simp) with h1686 | h1686
                                  · linarith only [h1566, h1686, hlam]
                                  · linarith only [h1565, h1686, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                          · linarith only [h0, h1, h1642, h1647, h1654, h1655, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1641, h1647, h1654, h3, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1642, h1650, h1651, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1641, h1645, h1647, h1650, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1565, h1647, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1695 | h1695
          · linarith only [h1565, h1642, h1695, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1697 | h1697
            · linarith only [h1697, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1699 | h1699
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1700 | h1700
                · linarith only [h0, h1566, h1700, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1702 | h1702
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1703 | h1703
                    · linarith only [h1, h1642, h1703, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1705 | h1705
                      · linarith only [h0, h1695, h1699, h1705, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1707 | h1707
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1708 | h1708
                          · linarith only [h1642, h1708, h3, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1710 | h1710
                            · linarith only [h0, h1699, h1705, h1710, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1712 | h1712
                              · linarith only [h0, h1699, h1707, h1708, h1710, h1712, h3, hlam]
                              · linarith only [h0, h1699, h1708, h1712, h3, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1641, h1699, h1707, h3, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h1641, h1642, h1702, hc13, hc35, hlam, hphi]
              · linarith only [h1565, h1699, hc12, hlam, hphi, u2elo0]
      · linarith only [h1565, h1641, h3, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1719 | h1719
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1720 | h1720
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1721 | h1721
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1722 | h1722
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
            · linarith only [h1723, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1725 | h1725
              · linarith only [h0, h1565, h1725, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1727 | h1727
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1729 | h1729
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1730 | h1730
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1731 | h1731
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1732 | h1732
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1733 | h1733
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1734 | h1734
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
                                  linarith only [h1565, h1727, h1731, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h3, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1565, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1565, h1731, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h0, hlam, p1735_1]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1723, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1725, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h0, h1565, h1731, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1565, h1719, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo2]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  rcases p1735_3 (m.d 0 2) (by simp) with h1750 | h1750
                                  · linarith only [h1750, h3, hlam]
                                  · linarith only [h1719, h1750, hlam]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h0, h1727, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo3]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1727, h1732, h1734, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1735_1, u2elo3]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1731, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  rcases p1735_3 (m.d 0 2) (by simp) with h1757 | h1757
                                  · linarith only [h1565, h1757, hlam]
                                  · linarith only [h1719, h1757, hlam]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1719, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1727, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1732, hlam, p1735_0]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [h1733, hlam, p1735_1]
                                · have p1735_0 := h1735c.1
                                  have p1735_1 := h1735c.2.1
                                  have p1735_2 := h1735c.2.2.1
                                  have p1735_3 := h1735c.2.2.2
                                  linarith only [hlam, p1735_0]
                              · linarith only [h1719, h1733, h1734, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h1565, h1727, h1730, h1733, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1565, h1721, h1727, h1731, h1732, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1, h1728, h1731, h3, hlam]
                      · linarith only [h1565, h1719, h1722, h1725, h1727, h1730, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1721, h1728, h1729, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1720, h1723, h1727, h1728, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1565, h1719, h1727, hc12, hlam, hphi, u2elo3]
          · linarith only [h1565, h1719, h1722, hlam]
        · linarith only [h1719, h1721, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1775 | h1775
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1776 | h1776
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1777 | h1777
            · linarith only [h1777, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1779 | h1779
              · linarith only [h0, h1565, h1779, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1781 | h1781
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1782 | h1782
                  · linarith only [h1, h1720, h1775, h1782, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1784 | h1784
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1785 | h1785
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1786 | h1786
                        · linarith only [h0, h1720, h1781, h1786, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1788 | h1788
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1789 | h1789
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1790 | h1790
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
                                  linarith only [h1781, h1786, h1788, h1790, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h3, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1565, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1786, h1788, h1790, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1791_1]
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
                                  linarith only [h1777, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1779, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h0, h1786, h1788, h1790, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1786, hc02, hc34, hlam, hphi, ht23, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1786, hc12, hc34, hlam, hphi, ht23, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1786, hlam, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  rcases p1791_3 (m.d 0 2) (by simp) with h1806 | h1806
                                  · linarith only [h1806, h3, hlam]
                                  · linarith only [h1719, h1806, hlam]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h0, h1781, h1788, h1790, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1791_1, u2elo3]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1781, h1788, h1790, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1791_1, u2elo3]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h0, h1781, h1788, h1790, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1791_1, u2elo3]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  rcases p1791_3 (m.d 0 2) (by simp) with h1813 | h1813
                                  · linarith only [h1565, h1813, hlam]
                                  · linarith only [h1719, h1813, hlam]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1719, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1781, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1788, hlam, p1791_0]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [h1789, hlam, p1791_1]
                                · have p1791_0 := h1791c.1
                                  have p1791_1 := h1791c.2.1
                                  have p1791_2 := h1791c.2.2.1
                                  have p1791_3 := h1791c.2.2.2
                                  linarith only [hlam, p1791_0]
                              · linarith only [h1720, h1776, h1790, hlam]
                            · linarith only [h1565, h1719, h1785, h1789, h2, hlam]
                          · linarith only [h1775, h1788, h3, hlam]
                      · linarith only [h1719, h1776, h1777, h1782, h1785, h3, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1720, h1775, h1777, h1781, h1784, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1719, h1781, h3, hc12, hlam, hphi, u2elo2]
          · linarith only [h1719, h1720, h1776, h3, hlam]
        · linarith only [h1719, h1775, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1829 | h1829
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1830 | h1830
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1831 | h1831
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1832 | h1832
            · linarith only [h1832, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1834 | h1834
              · linarith only [h0, h1565, h1834, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1836 | h1836
                · linarith only [h0, h1719, h1836, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1838 | h1838
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1840 | h1840
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1841 | h1841
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1842 | h1842
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1843 | h1843
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1844 | h1844
                              · rcases h2bigk with h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1719, h1841, h1843, hc12, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h3, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1565, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1719, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h0, hlam, p1845_1]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1832, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1834, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1836, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h0, h1565, hc12, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h0, h1719, hc12, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1845_1, u2elo3]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1845_1, u2elo3]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1841, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1719, h1836, h1841, h2, hc12, hlam, hphi, p1845_1, u2elo2]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1845_1, u2elo4]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1845_1, u2elo4]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1842, hlam, p1845_0]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [h1843, hlam, p1845_1]
                                · have p1845_0 := h1845c.1
                                  have p1845_1 := h1845c.2.1
                                  have p1845_2 := h1845c.2.2.1
                                  have p1845_3 := h1845c.2.2.2
                                  linarith only [hlam, p1845_0]
                              · rcases h2bigk with h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1871_1, u2elo0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h3, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1565, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1719, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, hlam, p1871_1]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1832, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1834, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1836, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1871_1, u2elo2]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1871_1, u2elo2]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, h1565, hc12, hlam, hphi, p1871_1, u2elo2]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, h1719, hc12, hlam, hphi, p1871_1, u2elo2]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1871_1, u2elo3]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1871_1, u2elo3]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1841, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, h1719, h1841, hc12, hlam, hphi, p1871_1, u2elo2]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1871_1, u2elo4]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1871_1, u2elo4]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1842, hlam, p1871_0]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [h1843, hlam, p1871_1]
                                · have p1871_0 := h1871c.1
                                  have p1871_1 := h1871c.2.1
                                  have p1871_2 := h1871c.2.2.1
                                  have p1871_3 := h1871c.2.2.2
                                  linarith only [hlam, p1871_0]
                            · linarith only [h0, h1, h1565, h1838, h1840, h1843, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1830, h1842, h3, hlam]
                        · linarith only [h1829, h1841, h3, hlam]
                      · linarith only [h1829, h1831, h1834, h1840, h3, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1830, h1838, h1839, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1829, h1832, h1838, h3, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1903 | h1903
            · linarith only [h0, h1903, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1905 | h1905
              · linarith only [h0, h1565, h1905, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1907 | h1907
                · linarith only [h0, h1719, h1907, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1909 | h1909
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1910 | h1910
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1911 | h1911
                      · linarith only [h1, h1565, h1831, h1909, h1911, h3, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1913 | h1913
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1914 | h1914
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1915 | h1915
                            · linarith only [h0, h1565, h1831, h1915, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1917 | h1917
                              · linarith only [h0, h1565, h1915, h1917, hc12, hc34, hlam, hphi, ht23]
                              · rcases h2bigk with h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1919_1, u2elo0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h3, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1565, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1719, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, hlam, p1919_1]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1903, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1905, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1907, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1919_1, u2elo2]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1919_1, u2elo2]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, h1565, hc12, hlam, hphi, p1919_1, u2elo2]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, h1719, hc12, hlam, hphi, p1919_1, u2elo2]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1919_1, u2elo3]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1919_1, u2elo3]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1913, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1915, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1919_1, u2elo4]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1919_1, u2elo4]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h1914, hlam, p1919_0]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [h0, h1565, h1914, hc12, hlam, hphi, p1919_1, u2elo2]
                                · have p1919_0 := h1919c.1
                                  have p1919_1 := h1919c.2.1
                                  have p1919_2 := h1919c.2.2.1
                                  have p1919_3 := h1919c.2.2.2
                                  linarith only [hlam, p1919_0]
                          · linarith only [h1, h1910, h1914, h3, hlam]
                        · linarith only [h1829, h1913, h3, hlam]
                    · linarith only [h1830, h1909, h1910, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1829, h1903, h1909, h3, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1949 | h1949
          · linarith only [h1829, h1830, h1949, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1951 | h1951
            · linarith only [h0, h1951, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1953 | h1953
              · linarith only [h0, h1565, h1953, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1955 | h1955
                · linarith only [h0, h1719, h1955, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1957 | h1957
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1958 | h1958
                    · linarith only [h1, h1830, h1958, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1960 | h1960
                      · linarith only [h1565, h1949, h1953, h1960, hc02, hlam, hphi, u2elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1963 | h1963
                          · linarith only [h1, h1830, h1957, h1963, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1965 | h1965
                            · linarith only [h0, h1565, h1949, h1962, h1963, h1965, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1967 | h1967
                              · linarith only [h1, h1957, h1965, h1967, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h2bigk with h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1565, hc12, hlam, hphi, p1969_1, u2elo3]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h3, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1565, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1719, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h0, hlam, p1969_1]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1951, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1953, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1955, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1963, h1967, hc02, hc45, hlam, hphi, ht23, ht34, p1969_1]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1963, h1967, hc12, hc45, hlam, hphi, ht23, ht34, p1969_1]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1963, h1967, hc24, hc45, hlam, hphi, p1969_1]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1963, hlam, p1969_1]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1969_1, u2elo3]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1969_1, u2elo3]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1962, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1965, hlam, p1969_0]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p1969_1, u2elo4]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hc12, hlam, hphi, p1969_1, u2elo4]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h1, h1957, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1969_1, u2elo4]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [h0, h1565, hc12, hlam, hphi, p1969_1, u2elo4]
                                · have p1969_0 := h1969c.1
                                  have p1969_1 := h1969c.2.1
                                  have p1969_2 := h1969c.2.2.1
                                  have p1969_3 := h1969c.2.2.2
                                  linarith only [hlam, p1969_0]
                        · linarith only [h0, h1, h1957, h1962, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1829, h1830, h1957, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1997 | h1997
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1998 | h1998
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1999 | h1999
            · linarith only [h0, h1999, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2001 | h2001
              · linarith only [h0, h1565, h2001, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2003 | h2003
                · linarith only [h0, h1719, h2003, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2005 | h2005
                  · linarith only [h1, h1829, h1997, h2005, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2007 | h2007
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2008 | h2008
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2009 | h2009
                        · linarith only [h1, h1829, h2007, h2009, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2011 | h2011
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2012 | h2012
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2013 | h2013
                              · rcases h2bigk with h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h1719, h2011, hc12, hlam, hphi, p2014_1, u2elo2]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h3, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h1565, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h1719, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, hlam, p2014_1]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h1999, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2001, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2003, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2009, hc02, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2009, hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2009, hlam, p2014_1]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, h1719, h2009, hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, h1719, hc12, hlam, hphi, p2014_1, u2elo3]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h0, h2011, hc12, hlam, hphi, p2014_1, u2elo2]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2009, h2011, hc12, hc34, hlam, hphi, ht23, p2014_1]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2011, hlam, p2014_0]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [h2012, hlam, p2014_1]
                                · have p2014_0 := h2014c.1
                                  have p2014_1 := h2014c.2.1
                                  have p2014_2 := h2014c.2.2.1
                                  have p2014_3 := h2014c.2.2.2
                                  linarith only [hlam, p2014_0]
                              · linarith only [h0, h2009, h2013, h3, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1565, h1997, h2, h2008, h2009, h2012, h3, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h2007, h2011, h3, hlam]
                      · linarith only [h1565, h1998, h2005, h2007, h2008, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1997, h1999, h2007, h3, hc12, hlam, hphi, u2elo2]
          · linarith only [h1829, h1997, h1998, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2046 | h2046
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2047 | h2047
            · linarith only [h0, h2047, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2049 | h2049
              · linarith only [h0, h1565, h2049, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2051 | h2051
                · linarith only [h1, h1719, h1997, h2047, h2051, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2053 | h2053
                  · linarith only [h1, h1829, h2053, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2055 | h2055
                    · linarith only [h1, h1997, h2055, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2057 | h2057
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2058 | h2058
                        · linarith only [h1, h1829, h2047, h2058, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2060 | h2060
                          · linarith only [h1, h1997, h2047, h2060, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2062 | h2062
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2063 | h2063
                              · rcases h2bigk with h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c | h2064c
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hc12, hlam, hphi, p2064_1, u2elo0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h3, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h1565, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h1719, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, hlam, p2064_1]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2047, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2049, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2051, hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2060, h2062, hc02, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2060, h2062, hc12, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2058, hlam, p2064_1]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2060, hlam, p2064_1]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hc12, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hlam, p2064_0]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, h1719, hc12, hlam, hphi, p2064_1, u2elo3]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p2064_1, u2elo4]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hc12, hlam, hphi, p2064_1, u2elo4]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p2064_1, u2elo4]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [h2062, hlam, p2064_1]
                                · have p2064_0 := h2064c.1
                                  have p2064_1 := h2064c.2.1
                                  have p2064_2 := h2064c.2.2.1
                                  have p2064_3 := h2064c.2.2.2
                                  linarith only [hlam, p2064_0]
                              · linarith only [h1, h1565, h1829, h2046, h2047, h2063, hc12, hlam, hphi, u2elo3]
                            · linarith only [h0, h1565, h1719, h2, h2057, h2062, hc12, hlam, hphi, u2elo4]
                      · linarith only [h1565, h2046, h2049, h2057, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2093 | h2093
            · linarith only [h0, h2093, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2095 | h2095
              · linarith only [h0, h1565, h2095, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2097 | h2097
                · linarith only [h0, h1719, h2097, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2099 | h2099
                  · linarith only [h1, h1829, h2099, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2101 | h2101
                    · linarith only [h1, h1997, h2101, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2103 | h2103
                      · linarith only [h0, h1829, h2046, h2095, h2103, h3, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2105 | h2105
                        · linarith only [h0, h1829, h2105, h3, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2107 | h2107
                          · linarith only [h0, h1997, h2107, h3, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2109 | h2109
                            · linarith only [h0, h1829, h2046, h2109, h3, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2111 | h2111
                              · linarith only [h0, h2105, h2109, h2111, h3, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h2105, h2111, h3, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2114 | h2114
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2115 | h2115
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2116 | h2116
      · linarith only [h0, h2, h2116, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2118 | h2118
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2119 | h2119
          · linarith only [h1, h2, h2119, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2121 | h2121
            · linarith only [h0, h2, h2115, h2121, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2123 | h2123
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2124 | h2124
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2125 | h2125
                  · linarith only [h2116, h2125, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2, h2125, hc12, hlam, hphi, u2elo4]
                · linarith only [h2115, h2116, h2123, h2124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h2114, h2116, h2123, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2130 | h2130
          · linarith only [h1, h2, h2130, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2132 | h2132
            · linarith only [h0, h2, h2115, h2116, h2132, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2134 | h2134
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2135 | h2135
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2136 | h2136
                  · linarith only [h2116, h2136, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2, h2136, hc12, hlam, hphi, u2elo4]
                · linarith only [h2115, h2116, h2134, h2135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h2114, h2116, h2134, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2141 | h2141
      · linarith only [h0, h2, h2115, h2141, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2143 | h2143
        · linarith only [h2114, h2115, h2143, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
          · linarith only [h0, h2, h2114, h2115, h2145, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2147 | h2147
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2148 | h2148
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2149 | h2149
                · linarith only [h0, h2, h2115, h2149, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2151 | h2151
                  · linarith only [h0, h2, h2141, h2151, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h2, h2148, h2151, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h0, h2, h2114, h2115, h2147, h2148, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2155 | h2155
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2156 | h2156
                · linarith only [h0, h2, h2115, h2156, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2158 | h2158
                  · linarith only [h0, h2, h2141, h2158, hlam]
                  · linarith only [h0, h2, h2155, h2158, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h2114, h2115, h2155, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2162 | h2162
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2163 | h2163
      · linarith only [h1, h2, h2114, h2163, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2165 | h2165
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2166 | h2166
          · linarith only [h1, h2, h2166, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2168 | h2168
            · linarith only [h1, h2, h2114, h2162, h2168, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2170 | h2170
              · linarith only [h0, h2, h2114, h2170, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2172 | h2172
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2173 | h2173
                  · linarith only [h0, h2, h2163, h2173, hlam]
                  · linarith only [h1, h2, h2170, h2172, h2173, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2114, h2162, h2172, hc12, hlam, hphi, u2elo2]
        · linarith only [h2114, h2162, h2165, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2178 | h2178
      · linarith only [h0, h2, h2114, h2178, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2180 | h2180
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2181 | h2181
          · linarith only [h1, h2, h2181, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2183 | h2183
            · linarith only [h1, h2, h2180, h2183, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2185 | h2185
              · linarith only [h2114, h2185, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2187 | h2187
                · linarith only [h0, h2162, h2187, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2189 | h2189
                  · linarith only [h0, h2, h2178, h2189, hlam]
                  · linarith only [h1, h2, h2185, h2189, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2192 | h2192
          · linarith only [h1, h2, h2192, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2194 | h2194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2195 | h2195
              · linarith only [h2114, h2195, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2197 | h2197
                · linarith only [h0, h2, h2162, h2194, h2197, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2199 | h2199
                  · linarith only [h2178, h2199, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2, h2199, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2202 | h2202
              · linarith only [h0, h2114, h2202, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2204 | h2204
                · linarith only [h0, h2162, h2204, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                  · linarith only [h0, h2, h2114, h2178, h2206, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1, h2, h2202, h2206, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2

end R2N4
