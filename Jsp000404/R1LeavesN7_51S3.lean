import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1471 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1472 | h1472
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1473 | h1473
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1474 | h1474
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1475 | h1475
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1476 | h1476
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1477 | h1477
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1478 | h1478
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1479 | h1479
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1480 | h1480
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1481 | h1481
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1482 | h1482
                      · linarith only [h1474, h1479, h1482, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1474, h1479, h1481, h1482, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1485 | h1485
                      · linarith only [h1479, h1481, h1485, hlam]
                      · rcases h5bigk with h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h0, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, h1479, h1481, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, h1485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, h1479, h1481, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1474, h1476, h1478, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1474, h1476, h1478, h1479, h1481, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1474, h1476, h1478, h1485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1474, h1476, h1478, h1479, h1481, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1471, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1475, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo4]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1481, hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1472, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1477, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1480, hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1485, hlam, p1487_0]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1473, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1478, hlam, p1487_1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h0, h1473, h1474, h1476, h1478, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [h1474, h1476, h1478, h1485, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1487_1, u2elo1]
                        · have p1487_0 := h1487c.1
                          have p1487_1 := h1487c.2.1
                          have p1487_2 := h1487c.2.2.1
                          have p1487_3 := h1487c.2.2.2
                          linarith only [hlam, p1487_0]
                  · linarith only [h1474, h1477, h1479, h1480, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1514 | h1514
                  · linarith only [h1474, h1476, h1479, h1514, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1516 | h1516
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1517 | h1517
                      · rcases h5bigk with h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hlam, p1518_0]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h0, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, h1514, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h0, h1474, h1476, h1478, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1474, h1476, h1478, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hlam, p1518_0]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1474, h1476, h1478, h1514, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1474, h1476, h1478, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1474, h1476, h1478, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1471, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1475, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hlam, p1518_0]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1514, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo4]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1472, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1477, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1472, hc03, hc25, hlam, hphi, ht0b, ht5b, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hlam, p1518_0]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1474, h1476, h1517, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1518_1, u2elo1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1473, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1478, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1516, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [h1517, hlam, p1518_1]
                        · have p1518_0 := h1518c.1
                          have p1518_1 := h1518c.2.1
                          have p1518_2 := h1518c.2.2.1
                          have p1518_3 := h1518c.2.2.2
                          linarith only [hlam, p1518_0]
                      · linarith only [h1474, h1476, h1478, h1479, h1517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1545 | h1545
                      · linarith only [h1474, h1476, h1479, h1516, h1545, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1474, h1476, h1478, h1479, h1545, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · linarith only [h0, h1473, h1478, hlam]
            · linarith only [h0, h1472, h1477, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1550 | h1550
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1551 | h1551
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1552 | h1552
                · linarith only [h1476, h1550, h1552, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1554 | h1554
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1555 | h1555
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1556 | h1556
                      · rcases h5bigk with h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hlam, p1557_0]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h0, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h0, h1476, h1550, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h0, h1476, h1550, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h0, h1476, h1550, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1476, h1550, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hlam, p1557_0]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1476, h1550, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1476, h1550, h1556, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1476, h1550, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1471, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1475, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hlam, p1557_0]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1556, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1557_1, u2elo4]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1557_1, u2elo4]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1472, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1550, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1554, hlam, p1557_0]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hlam, p1557_0]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1472, hc03, hc45, hlam, hphi, ht0b, ht5b, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1473, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1551, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1555, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [h1556, hlam, p1557_1]
                        · have p1557_0 := h1557c.1
                          have p1557_1 := h1557c.2.1
                          have p1557_2 := h1557c.2.2.1
                          have p1557_3 := h1557c.2.2.2
                          linarith only [hlam, p1557_0]
                      · linarith only [h0, h1476, h1550, h1556, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1552, h1554, h1555, hlam]
                  · linarith only [h1476, h1550, h1554, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1473, h1476, h1550, h1551, hlam]
            · linarith only [h0, h1472, h1550, hlam]
        · linarith only [h1471, h1475, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1589 | h1589
        · linarith only [h0, h1474, h1589, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h1471, h1589, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1592 | h1592
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1593 | h1593
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1594 | h1594
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1596 | h1596
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1597 | h1597
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1598 | h1598
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1599 | h1599
                    · linarith only [h1473, h1592, h1597, h1599, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1601 | h1601
                      · linarith only [h1597, h1599, h1601, hlam]
                      · rcases h5bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h0, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1473, h1594, h1596, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1473, h1594, h1596, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1473, hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h0, h1594, h1596, hc01, hc13, hlam, hphi, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1592, h1594, h1596, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1603_1, u2elo1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1592, h1594, h1596, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1603_1, u2elo1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1592, h1594, h1596, h1597, h1599, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1603_1, u2elo1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1471, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1593, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1603_1, u2elo4]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1599, hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1472, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1595, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1598, hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1601, hlam, p1603_0]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1596, hlam, p1603_1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1592, h1594, h1596, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1603_1, u2elo1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [h1592, h1594, h1596, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1603_1, u2elo1]
                        · have p1603_0 := h1603c.1
                          have p1603_1 := h1603c.2.1
                          have p1603_2 := h1603c.2.2.1
                          have p1603_3 := h1603c.2.2.2
                          linarith only [hlam, p1603_0]
                  · linarith only [h1472, h1473, h1592, h1594, h1596, h1597, h1598, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1630 | h1630
                  · linarith only [h1592, h1594, h1597, h1630, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1632 | h1632
                    · linarith only [h1473, h1592, h1594, h1597, h1632, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1634 | h1634
                      · linarith only [h1472, h1473, h1592, h1594, h1630, h1634, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1592, h1594, h1596, h1597, h1634, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1637 | h1637
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1638 | h1638
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1639 | h1639
                    · linarith only [h1592, h1596, h1637, h1639, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1641 | h1641
                      · linarith only [h0, h1592, h1594, h1596, h1641, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases h5bigk with h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h0, hlam, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h0, h1596, h1637, h1639, hc34, hc45, hlam, hphi, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1471, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1643_1, u2elo0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1473, hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h0, h1596, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1593, h1637, h1639, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1643_1, u2elo1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1592, h1595, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1643_1, u2elo1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1596, hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1471, hlam, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1593, hlam, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1643_1, u2elo4]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1639, hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1472, hlam, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1595, hlam, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1638, hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1641, hlam, p1643_0]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1637, h1639, hc34, hc45, hlam, hphi, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [h1641, hc34, hc45, hlam, hphi, p1643_1]
                        · have p1643_0 := h1643c.1
                          have p1643_1 := h1643c.2.1
                          have p1643_2 := h1643c.2.2.1
                          have p1643_3 := h1643c.2.2.2
                          linarith only [hlam, p1643_0]
                  · linarith only [h1592, h1595, h1637, h1638, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1670 | h1670
                  · linarith only [h1592, h1594, h1637, h1670, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1672 | h1672
                    · linarith only [h0, h1596, h1672, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1674 | h1674
                      · linarith only [h1473, h1592, h1594, h1674, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases h5bigk with h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h0, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1471, h1637, h1672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1676_1, u2elo0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1471, h1637, h1674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1676_1, u2elo0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1473, hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1593, h1637, h1672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1676_1, u2elo1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1592, h1595, h1637, h1674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1676_1, u2elo1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1596, hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1471, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1593, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1670, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1672, hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1472, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1595, hlam, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1637, h1672, hc23, hc35, hlam, hphi, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1674, hlam, p1676_0]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1637, h1672, hc23, hc45, hlam, hphi, ht34, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [h1670, hc23, hc45, hlam, hphi, ht34, p1676_1]
                        · have p1676_0 := h1676c.1
                          have p1676_1 := h1676c.2.1
                          have p1676_2 := h1676c.2.2.1
                          have p1676_3 := h1676c.2.2.2
                          linarith only [hlam, p1676_0]
            · linarith only [h0, h1472, h1595, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1703 | h1703
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1704 | h1704
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1705 | h1705
                · linarith only [h0, h1594, h1703, h1705, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1707 | h1707
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1708 | h1708
                    · linarith only [h1471, h1473, h1708, hlam]
                    · linarith only [h1705, h1707, h1708, hlam]
                  · linarith only [h1594, h1703, h1707, hc23, hc34, hlam, hphi]
              · linarith only [h1594, h1703, h1704, hlam]
            · linarith only [h0, h1472, h1703, hlam]
        · linarith only [h1471, h1593, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1715 | h1715
        · linarith only [h0, h1592, h1715, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h1471, h1715, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1718 | h1718
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1719 | h1719
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1720 | h1720
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1722 | h1722
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1723 | h1723
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                  · linarith only [h1472, h1719, h1725, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h1719, h1722, h1724, h1725, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1728 | h1728
                  · linarith only [h1472, h1724, h1728, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1730 | h1730
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1731 | h1731
                      · rcases h5bigk with h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hlam, p1732_0]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h0, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1472, h1719, h1721, h1731, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1472, hlam, p1732_0]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1472, h1719, h1721, h1731, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1719, h1721, h1723, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hlam, p1732_0]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1719, h1721, h1723, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1472, h1719, h1721, h1723, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1719, h1721, h1723, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1471, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1720, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hlam, p1732_0]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1728, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo4]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1722, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1719, h1722, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hlam, p1732_0]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1719, h1721, h1731, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1732_1, u2elo1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1718, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1723, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1730, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [h1731, hlam, p1732_1]
                        · have p1732_0 := h1732c.1
                          have p1732_1 := h1732c.2.1
                          have p1732_2 := h1732c.2.2.1
                          have p1732_3 := h1732c.2.2.2
                          linarith only [hlam, p1732_0]
                      · linarith only [h1472, h1718, h1719, h1722, h1724, h1731, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1759 | h1759
                      · linarith only [h1719, h1721, h1724, h1730, h1759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1472, h1718, h1719, h1722, h1724, h1759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · linarith only [h0, h1472, h1718, h1719, h1722, h1723, hc01, hlam, hphi, ht12, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1763 | h1763
              · linarith only [h1721, h1722, h1763, hlam]
              · linarith only [h0, h1718, h1763, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1766 | h1766
            · linarith only [h1472, h1721, h1766, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1768 | h1768
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1769 | h1769
                · linarith only [h1719, h1721, h1769, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h0, h1766, h1771, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1773 | h1773
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1774 | h1774
                      · rcases h5bigk with h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h0, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1471, h1771, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1775_1, u2elo0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1472, hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1471, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1775_1, u2elo0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1720, h1771, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1775_1, u2elo1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1766, hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1720, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1775_1, u2elo1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1471, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1720, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1771, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1471, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1775_1, u2elo0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1471, h1771, h1774, hc23, hc34, hlam, hphi, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h0, h1774, hc01, hc34, hlam, hphi, ht12, ht23, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1771, h1774, hc23, hc34, hlam, hphi, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [hlam, p1775_0]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          rcases p1775_3 (m.d 0 5) (by simp) with h1795 | h1795
                          · linarith only [h1472, h1795, hlam]
                          · linarith only [h1718, h1795, hlam]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1718, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1768, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1773, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [h1774, hlam, p1775_1]
                        · have p1775_0 := h1775c.1
                          have p1775_1 := h1775c.2.1
                          have p1775_2 := h1775c.2.2.1
                          have p1775_3 := h1775c.2.2.2
                          linarith only [hlam, p1775_0]
                      · linarith only [h1719, h1721, h1773, h1774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1804 | h1804
                      · rcases h5bigk with h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h0, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h0, h1766, h1769, h1773, hc23, hc35, hlam, hphi, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1472, hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1471, h1769, h1773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u2elo0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h0, h1766, hc01, hc35, hlam, hphi, ht12, ht23, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1720, h1769, h1773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u2elo1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1766, hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1768, h1769, h1773, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1471, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1720, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1771, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1773, hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1718, h1769, h1773, hc23, hc35, hlam, hphi, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1769, h1773, hc23, hc35, hlam, hphi, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [hlam, p1805_0]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1769, h1773, h1804, hc23, hc34, hlam, hphi, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1718, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1768, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1769, h1773, hc23, hc45, hlam, hphi, ht34, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [h1804, hlam, p1805_1]
                        · have p1805_0 := h1805c.1
                          have p1805_1 := h1805c.2.1
                          have p1805_2 := h1805c.2.2.1
                          have p1805_3 := h1805c.2.2.2
                          linarith only [hlam, p1805_0]
                      · linarith only [h1721, h1768, h1804, hlam]
              · linarith only [h0, h1718, h1768, hlam]
        · linarith only [h1471, h1720, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1834 | h1834
        · linarith only [h0, h1719, h1834, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h1471, h1834, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1837 | h1837
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1838 | h1838
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1839 | h1839
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1840 | h1840
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1841 | h1841
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1842 | h1842
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1843 | h1843
                  · linarith only [h1472, h1837, h1843, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h1837, h1840, h1842, h1843, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1846 | h1846
                  · linarith only [h1472, h1842, h1846, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1848 | h1848
                    · linarith only [h1718, h1837, h1839, h1842, h1848, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1850 | h1850
                      · linarith only [h1837, h1839, h1842, h1848, h1850, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1837, h1839, h1841, h1842, h1850, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1854 | h1854
                  · linarith only [h1472, h1837, h1854, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h1837, h1840, h1853, h1854, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1857 | h1857
                  · linarith only [h1472, h1853, h1857, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1859 | h1859
                    · linarith only [h1839, h1841, h1853, h1859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1861 | h1861
                      · linarith only [h1839, h1841, h1861, hlam]
                      · rcases h5bigk with h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h0, hlam, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1471, h1859, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1863_1, u2elo0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1472, hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1718, hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1838, h1859, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1863_1, u2elo1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1837, h1840, h1853, h1861, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1863_1, u2elo1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1841, hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1471, hlam, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1838, hlam, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1857, hlam, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1859, hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1840, hlam, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1837, h1840, h1853, h1859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1863_1, u2elo1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1861, hlam, p1863_0]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h0, h1472, h1837, h1840, hc01, hc03, hc45, hlam, hphi, ht12, ht34, p1863_1, u2elo1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1853, h1859, hc23, hc45, hlam, hphi, ht34, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [h1472, hc03, hc45, hlam, hphi, ht34, p1863_1]
                        · have p1863_0 := h1863c.1
                          have p1863_1 := h1863c.2.1
                          have p1863_2 := h1863c.2.2.1
                          have p1863_3 := h1863c.2.2.2
                          linarith only [hlam, p1863_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1889 | h1889
              · linarith only [h1839, h1840, h1889, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1891 | h1891
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1892 | h1892
                  · linarith only [h1837, h1840, h1892, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1894 | h1894
                    · linarith only [h0, h1889, h1894, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1896 | h1896
                      · linarith only [h0, h1837, h1889, h1891, h1896, hc01, hc13, hlam, hphi]
                      · rcases h5bigk with h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h0, hlam, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1471, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1898_1, u2elo0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1472, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1718, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h0, h1840, h1896, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1838, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1898_1, u2elo1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1840, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1889, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1471, hlam, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1838, hlam, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1892, hlam, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1894, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h0, h1896, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h0, h1896, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1892, h1896, hc23, hc45, hlam, hphi, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1896, hlam, p1898_0]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1471, h1891, h1892, hc34, hc45, hlam, hphi, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1891, h1892, hc34, hc45, hlam, hphi, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [h1472, hc03, hc45, hlam, hphi, ht34, p1898_1]
                        · have p1898_0 := h1898c.1
                          have p1898_1 := h1898c.2.1
                          have p1898_2 := h1898c.2.2.1
                          have p1898_3 := h1898c.2.2.2
                          linarith only [hlam, p1898_0]
                · linarith only [h1839, h1840, h1891, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1925 | h1925
            · linarith only [h1472, h1839, h1925, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1927 | h1927
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1928 | h1928
                · linarith only [h1837, h1839, h1928, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1930 | h1930
                  · linarith only [h0, h1925, h1930, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1932 | h1932
                    · linarith only [h1471, h1718, h1932, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1934 | h1934
                      · rcases h5bigk with h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, h1925, h1928, h1932, hc23, hc35, hlam, hphi, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1472, hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1718, hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, h1925, hc01, hc35, hlam, hphi, ht12, ht23, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1838, h1928, h1932, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1935_1, u2elo1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1925, hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1838, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1935_1, u2elo1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1471, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1838, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1930, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1932, hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1928, h1932, hc23, hc35, hlam, hphi, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [hlam, p1935_0]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1928, h1932, h1934, hc23, hc34, hlam, hphi, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1927, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1928, h1932, hc23, hc45, hlam, hphi, ht34, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [h1934, hlam, p1935_1]
                        · have p1935_0 := h1935c.1
                          have p1935_1 := h1935c.2.1
                          have p1935_2 := h1935c.2.2.1
                          have p1935_3 := h1935c.2.2.2
                          linarith only [hlam, p1935_0]
                      · linarith only [h1839, h1927, h1934, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                · linarith only [h1837, h1839, h1962, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1964 | h1964
                  · linarith only [h1472, h1837, h1839, h1964, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1966 | h1966
                    · linarith only [h0, h1927, h1966, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1968 | h1968
                      · rcases h5bigk with h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hlam, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1471, h1966, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1969_1, u2elo0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1472, hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1718, hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1838, h1966, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1969_1, u2elo1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1925, hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1927, hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1471, hlam, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1838, hlam, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1964, hlam, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1966, hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1962, h1966, hc23, hc35, hlam, hphi, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [hlam, p1969_0]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1839, h1927, h1968, hc13, hc34, hlam, hphi, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1962, h1966, hc23, hc45, hlam, hphi, ht34, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [h1968, hlam, p1969_1]
                        · have p1969_0 := h1969c.1
                          have p1969_1 := h1969c.2.1
                          have p1969_2 := h1969c.2.2.1
                          have p1969_3 := h1969c.2.2.2
                          linarith only [hlam, p1969_0]
                      · rcases h5bigk with h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c
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
                          linarith only [h1471, h1962, h1966, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1995_1, u2elo0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1472, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1718, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1838, h1962, h1966, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1995_1, u2elo1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1925, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1927, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1471, hlam, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1838, hlam, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1964, hlam, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1966, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h0, h1968, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h0, h1968, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1962, h1966, h1968, hc23, hc45, hlam, hphi, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1968, hlam, p1995_0]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1962, h1966, hc23, hc45, hlam, hphi, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [h1472, hc03, hc45, hlam, hphi, ht34, p1995_1]
                        · have p1995_0 := h1995c.1
                          have p1995_1 := h1995c.2.1
                          have p1995_2 := h1995c.2.2.1
                          have p1995_3 := h1995c.2.2.2
                          linarith only [hlam, p1995_0]
        · linarith only [h1471, h1838, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2022 | h2022
        · linarith only [h0, h1837, h2022, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h1471, h2022, hc12, hlam, hphi, u2elo0]

end R2N4
