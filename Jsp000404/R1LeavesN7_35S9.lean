import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1387 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1388 | h1388
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1389 | h1389
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1390 | h1390
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1391 | h1391
        · linarith only [h1, h1388, h1391, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1395 | h1395
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1396 | h1396
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1397 | h1397
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1398 | h1398
                    · linarith only [h0, h1, h1393, h1398, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases h2bigk with h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1, hc12, hc23, hlam, hphi, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1, h1396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1, h1397, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1400_1, u5ehi3]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h0, hlam, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1391, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h0, h1396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h0, h1, h1397, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1400_1, u5ehi3]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hc02, hc23, hlam, hphi, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        rcases p1400_3 (m.d 0 2) (by simp) with h1414 | h1414
                        · linarith only [h1, h1414, hlam]
                        · linarith only [h1387, h1414, hlam]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1397, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1400_1, u5ehi3]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1387, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1393, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1396, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1398, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1388, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1394, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1397, hlam, p1400_0]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [h1394, h1396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1400_1]
                      · have p1400_0 := h1400c.1
                        have p1400_1 := h1400c.2.1
                        have p1400_2 := h1400c.2.2.1
                        have p1400_3 := h1400c.2.2.2
                        linarith only [hlam, p1400_0]
                  · linarith only [h0, h1, h1394, h1397, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h0, h1, h1394, h1396, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h1389, h1391, h1394, h1395, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h1, h1388, h1394, hc12, hc23, hlam, hphi]
          · linarith only [h1, h1387, h1393, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1433 | h1433
        · linarith only [h1, h1388, h1433, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1435 | h1435
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1436 | h1436
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1437 | h1437
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1438 | h1438
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1439 | h1439
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1440 | h1440
                    · linarith only [h0, h1, h1435, h1440, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases h2bigk with h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1, hc12, hc23, hlam, hphi, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1, h1438, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1, h1439, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1442_1, u5ehi3]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h0, hlam, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1433, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h0, h1438, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h0, h1, h1439, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1442_1, u5ehi3]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hc02, hc23, hlam, hphi, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        rcases p1442_3 (m.d 0 2) (by simp) with h1456 | h1456
                        · linarith only [h1, h1456, hlam]
                        · linarith only [h1387, h1456, hlam]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1439, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1442_1, u5ehi3]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1387, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1435, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1438, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1440, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1388, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1436, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h1439, hlam, p1442_0]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [h0, h1436, h1438, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1442_1]
                      · have p1442_0 := h1442c.1
                        have p1442_1 := h1442c.2.1
                        have p1442_2 := h1442c.2.2.1
                        have p1442_3 := h1442c.2.2.2
                        linarith only [hlam, p1442_0]
                  · linarith only [h0, h1, h1436, h1439, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h0, h1, h1436, h1438, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h1, h1388, h1389, h1390, h1433, h1436, h1437, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h1, h1388, h1436, hc12, hc23, hlam, hphi]
          · linarith only [h1, h1387, h1435, hc12, hc23, hlam, hphi]
    · linarith only [h1, h1387, h1389, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1476 | h1476
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1477 | h1477
      · linarith only [h1387, h1388, h1477, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1479 | h1479
        · linarith only [h0, h1, h1479, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1481 | h1481
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1482 | h1482
            · linarith only [h0, h1388, h1482, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1484 | h1484
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1485 | h1485
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1486 | h1486
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1487 | h1487
                    · linarith only [h0, h1388, h1477, h1481, h1486, h1487, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases h2bigk with h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1388, h1487, hc12, hc45, hlam, hphi, ht23, ht34, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1388, h1485, h1487, hc34, hc45, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1388, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, hlam, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1479, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1485, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1482, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hc02, hc23, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 2) (by simp) with h1503 | h1503
                        · linarith only [h1, h1503, hlam]
                        · linarith only [h1387, h1503, hlam]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1388, h1481, h1485, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1387, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1481, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1485, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1487, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h1481, h1485, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1481, h1485, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1486, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1485, h1487, hc34, hc45, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1517 | h1517
                    · linarith only [h0, h1481, h1517, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h2bigk with h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1, h1486, hc12, hc35, hlam, hphi, ht23, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1, h1485, h1486, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1388, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1479, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h0, h1485, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1482, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1486, hc02, hc35, hlam, hphi, ht23, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1486, hc12, hc35, hlam, hphi, ht23, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1485, h1486, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1486, hlam, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1387, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1481, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1485, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1517, hlam, p1519_0]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hc02, hc25, hlam, hphi, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1481, h1485, h1517, hc34, hc45, hlam, hphi, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1517, hc23, hc45, hlam, hphi, ht34, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [h1485, h1517, hc34, hc45, hlam, hphi, p1519_1]
                      · have p1519_0 := h1519c.1
                        have p1519_1 := h1519c.2.1
                        have p1519_2 := h1519c.2.2.1
                        have p1519_3 := h1519c.2.2.2
                        linarith only [hlam, p1519_0]
                · linarith only [h1, h1476, h1485, hlam]
              · linarith only [h1476, h1477, h1479, h1481, h1484, hc24, hc45, hlam, hphi]
          · linarith only [h1, h1387, h1481, hc12, hc23, hlam, hphi]
    · linarith only [h1, h1387, h1476, hlam]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1387 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1549 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1550 | h1550
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1551 | h1551
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1552 | h1552
      · linarith only [h1, h1549, h1552, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1554 | h1554
        · linarith only [h0, h1387, h1554, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1556 | h1556
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1557 | h1557
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1558 | h1558
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1559 | h1559
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1560 | h1560
                  · rcases h2bigk with h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c | h1561c
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1556, h1559, hc02, hlam, hphi, ht0b, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1387, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1387, h1558, h1559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h0, hlam, p1561_1]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1552, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1554, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1559, hc12, hlam, hphi, ht01, ht0b, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1561_1]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1561_1]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1387, h1549, h1559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h0, h1556, h1559, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1556, h1559, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1558, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1558, h1559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1561_1, u5ehi3]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1549, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1556, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1559, hlam, p1561_0]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [h1560, hlam, p1561_1]
                    · have p1561_0 := h1561c.1
                      have p1561_1 := h1561c.2.1
                      have p1561_2 := h1561c.2.2.1
                      have p1561_3 := h1561c.2.2.2
                      linarith only [hlam, p1561_0]
                  · linarith only [h0, h1387, h1556, h1559, h1560, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                · linarith only [h0, h1, h1556, h1559, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h1, h1550, h1558, hlam]
            · linarith only [h1550, h1552, h1556, h1557, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
          · linarith only [h1387, h1549, h1556, hc12, hc24, hlam, hphi]
    · linarith only [h1387, h1549, h1551, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1593 | h1593
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1594 | h1594
      · linarith only [h1, h1549, h1594, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1596 | h1596
        · linarith only [h0, h1387, h1596, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1598 | h1598
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1599 | h1599
            · linarith only [h0, h1, h1550, h1598, h1599, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1601 | h1601
              · linarith only [h0, h1, h1550, h1598, h1601, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h0, h1, h1598, h1601, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · linarith only [h1, h1549, h1598, hc12, hc23, hlam, hphi]
    · linarith only [h1, h1549, h1550, h1593, hlam]

end R2N4
