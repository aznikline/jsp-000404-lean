import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S0
import Jsp000404.R1LeavesN7_11S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 3 4 (by decide) (by decide) with h1334 | h1334
  · linarith only [h11, h1334, h9, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1336 | h1336
    · linarith only [h1336, h355, h9, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h1338 | h1338
      · linarith only [h10, h1338, h416, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h1340 | h1340
        · rcases h2bigk with h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            rcases p1341_3 (m.d 0 2) (by simp) with h1343 | h1343
            · rcases p1341_3 (m.d 1 2) (by simp) with h1344 | h1344
              · linarith only [h0, h1344, hlam]
              · rcases p1341_3 (m.d 2 3) (by simp) with h1346 | h1346
                · linarith only [h1346, h3, hlam]
                · rcases p1341_3 (m.d 2 4) (by simp) with h1348 | h1348
                  · linarith only [h1348, h4, hlam]
                  · rcases p1341_3 (m.d 2 5) (by simp) with h1350 | h1350
                    · linarith only [h1350, h5, hlam]
                    · rcases h3bigk with h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h11, h1340, h416, h6, hlam, p1352_2]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h11, h1340, h416, h6, h9, hlam, p1352_2]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h1338, h1340, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p1352_1]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        rcases p1352_3 (m.d 0 3) (by simp) with h1357 | h1357
                        · rcases p1352_3 (m.d 1 3) (by simp) with h1358 | h1358
                          · linarith only [h1, h1358, hlam]
                          · rcases p1352_3 (m.d 2 3) (by simp) with h1360 | h1360
                            · linarith only [h1360, h3, hlam]
                            · rcases p1352_3 (m.d 3 4) (by simp) with h1362 | h1362
                              · linarith only [h1362, h6, hlam]
                              · linarith only [h1340, h1362, hlam]
                        · linarith only [h1357, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h1, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h11, h1340, h416, hc23, hc34, hlam, hphi, p1352_1]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h11, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h355, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h3, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h9, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h1334, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h1336, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h6, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        rcases p1352_3 (m.d 0 3) (by simp) with h1377 | h1377
                        · rcases p1352_3 (m.d 1 3) (by simp) with h1378 | h1378
                          · linarith only [h1378, hlam, p1352_0]
                          · rcases p1352_3 (m.d 2 3) (by simp) with h1380 | h1380
                            · linarith only [h1334, h1380, hlam]
                            · rcases p1352_3 (m.d 3 4) (by simp) with h1382 | h1382
                              · rcases p1352_3 (m.d 3 5) (by simp) with h1383 | h1383
                                · linarith only [h1340, h1383, hlam]
                                · linarith only [h1383, h355, hlam]
                              · linarith only [h1382, hlam, p1352_0]
                        · linarith only [h1, h1377, hlam]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        rcases p1352_3 (m.d 0 3) (by simp) with h1388 | h1388
                        · rcases p1352_3 (m.d 1 3) (by simp) with h1389 | h1389
                          · linarith only [h11, h1389, hlam]
                          · linarith only [h1389, h9, hlam]
                        · linarith only [h1388, h3, hlam]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h0, h11, h1340, h3, h416, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1352_1]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h7, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        rcases p1352_3 (m.d 0 3) (by simp) with h1396 | h1396
                        · rcases p1352_3 (m.d 1 3) (by simp) with h1397 | h1397
                          · linarith only [h1397, hlam, p1352_0]
                          · rcases p1352_3 (m.d 2 3) (by simp) with h1399 | h1399
                            · linarith only [h1336, h1399, hlam]
                            · rcases p1352_3 (m.d 3 4) (by simp) with h1401 | h1401
                              · rcases p1352_3 (m.d 3 5) (by simp) with h1402 | h1402
                                · rcases h5bigk with h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 5) (by simp) with h1405 | h1405
                                    · rcases p1403_3 (m.d 1 5) (by simp) with h1406 | h1406
                                      · linarith only [h1406, h2, hlam]
                                      · rcases p1403_3 (m.d 2 5) (by simp) with h1408 | h1408
                                        · linarith only [h1408, h5, hlam]
                                        · rcases p1403_3 (m.d 3 5) (by simp) with h1410 | h1410
                                          · linarith only [h1410, h7, hlam]
                                          · linarith only [h1410, h355, hlam]
                                    · linarith only [h1405, h2, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 5) (by simp) with h1414 | h1414
                                    · rcases p1403_3 (m.d 1 5) (by simp) with h1415 | h1415
                                      · linarith only [h1415, h2, hlam]
                                      · linarith only [h10, h1415, hlam]
                                    · linarith only [h1414, h5, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1352_1, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h11, h3, h416, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h2, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h355, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h416, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h5, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h10, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h1336, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h1338, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h7, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h11, h1340, h3, h416, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h8, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h11, h416, h9, hc23, hc45, hlam, hphi, ht34, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h1340, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                · linarith only [h1402, hlam, p1352_0]
                              · linarith only [h11, h1401, hlam]
                        · linarith only [h1, h1396, hlam]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        rcases p1352_3 (m.d 0 3) (by simp) with h1444 | h1444
                        · rcases p1352_3 (m.d 1 3) (by simp) with h1445 | h1445
                          · linarith only [h1445, h355, hlam]
                          · linarith only [h1445, h9, hlam]
                        · linarith only [h1444, h3, hlam]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [h1340, hlam, p1352_0]
                      · have p1352_0 := h1352c.1
                        have p1352_1 := h1352c.2.1
                        have p1352_2 := h1352c.2.2.1
                        have p1352_3 := h1352c.2.2.2
                        linarith only [hlam, p1352_0]
            · linarith only [h0, h1343, hlam]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h11, h1340, h3, h416, h6, h9, hlam, p1341_2]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h1338, h1340, h3, h6, hlam, p1341_2]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            rcases p1341_3 (m.d 0 2) (by simp) with h1454 | h1454
            · rcases p1341_3 (m.d 1 2) (by simp) with h1455 | h1455
              · linarith only [h0, h1455, hlam]
              · linarith only [h10, h1455, hlam]
            · linarith only [h1454, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h0, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            rcases p1341_3 (m.d 0 2) (by simp) with h1461 | h1461
            · rcases p1341_3 (m.d 1 2) (by simp) with h1462 | h1462
              · rcases p1341_3 (m.d 2 3) (by simp) with h1463 | h1463
                · linarith only [h1463, hlam, p1341_0]
                · rcases p1341_3 (m.d 2 4) (by simp) with h1465 | h1465
                  · linarith only [h0, h1338, h1340, h1465, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1341_1]
                  · linarith only [h1334, h1465, hlam]
              · linarith only [h1462, hlam, p1341_0]
            · linarith only [h1461, h3, hlam]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            rcases p1341_3 (m.d 0 2) (by simp) with h1470 | h1470
            · rcases p1341_3 (m.d 1 2) (by simp) with h1471 | h1471
              · rcases p1341_3 (m.d 2 3) (by simp) with h1472 | h1472
                · linarith only [h1472, h9, hlam]
                · rcases p1341_3 (m.d 2 4) (by simp) with h1474 | h1474
                  · linarith only [h1474, hlam, p1341_0]
                  · rcases p1341_3 (m.d 2 5) (by simp) with h1476 | h1476
                    · linarith only [h10, h1476, hlam]
                    · linarith only [h1338, h1476, hlam]
              · linarith only [h1471, hlam, p1341_0]
            · linarith only [h1470, h4, hlam]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            rcases p1341_3 (m.d 0 2) (by simp) with h1481 | h1481
            · rcases p1341_3 (m.d 1 2) (by simp) with h1482 | h1482
              · rcases p1341_3 (m.d 2 3) (by simp) with h1483 | h1483
                · linarith only [h1483, h9, hlam]
                · rcases p1341_3 (m.d 2 4) (by simp) with h1485 | h1485
                  · linarith only [h0, h1338, h1340, h1485, h3, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p1341_1]
                  · rcases p1341_3 (m.d 2 5) (by simp) with h1487 | h1487
                    · linarith only [h1487, hlam, p1341_0]
                    · rcases h3bigk with h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h11, h1340, h416, h6, hlam, p1489_2]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h11, h1340, h416, h6, h9, hlam, p1489_2]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h11, h1340, h3, h416, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 3) (by simp) with h1494 | h1494
                        · rcases p1489_3 (m.d 1 3) (by simp) with h1495 | h1495
                          · linarith only [h1, h1495, hlam]
                          · rcases p1489_3 (m.d 2 3) (by simp) with h1497 | h1497
                            · linarith only [h1497, h3, hlam]
                            · rcases p1489_3 (m.d 3 4) (by simp) with h1499 | h1499
                              · linarith only [h1499, h6, hlam]
                              · linarith only [h1340, h1499, hlam]
                        · linarith only [h1494, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h11, h1340, h416, hc23, hc34, hlam, hphi, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h11, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h355, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h3, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h9, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1334, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1336, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h6, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 3) (by simp) with h1514 | h1514
                        · rcases p1489_3 (m.d 1 3) (by simp) with h1515 | h1515
                          · linarith only [h1515, hlam, p1489_0]
                          · rcases p1489_3 (m.d 2 3) (by simp) with h1517 | h1517
                            · linarith only [h1334, h1517, hlam]
                            · rcases p1489_3 (m.d 3 4) (by simp) with h1519 | h1519
                              · rcases p1489_3 (m.d 3 5) (by simp) with h1520 | h1520
                                · linarith only [h1340, h1520, hlam]
                                · linarith only [h1520, h355, hlam]
                              · linarith only [h1519, hlam, p1489_0]
                        · linarith only [h1, h1514, hlam]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 3) (by simp) with h1525 | h1525
                        · rcases p1489_3 (m.d 1 3) (by simp) with h1526 | h1526
                          · linarith only [h11, h1526, hlam]
                          · linarith only [h1526, h9, hlam]
                        · linarith only [h1525, h3, hlam]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h0, h11, h1340, h3, h416, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1489_1]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h7, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 3) (by simp) with h1533 | h1533
                        · rcases p1489_3 (m.d 1 3) (by simp) with h1534 | h1534
                          · linarith only [h1534, hlam, p1489_0]
                          · rcases p1489_3 (m.d 2 3) (by simp) with h1536 | h1536
                            · linarith only [h1336, h1536, hlam]
                            · rcases p1489_3 (m.d 3 4) (by simp) with h1538 | h1538
                              · rcases p1489_3 (m.d 3 5) (by simp) with h1539 | h1539
                                · rcases h5bigk with h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    rcases p1540_3 (m.d 0 5) (by simp) with h1542 | h1542
                                    · rcases p1540_3 (m.d 1 5) (by simp) with h1543 | h1543
                                      · linarith only [h1543, h2, hlam]
                                      · rcases p1540_3 (m.d 2 5) (by simp) with h1545 | h1545
                                        · linarith only [h1545, h5, hlam]
                                        · rcases p1540_3 (m.d 3 5) (by simp) with h1547 | h1547
                                          · linarith only [h1547, h7, hlam]
                                          · linarith only [h1547, h355, hlam]
                                    · linarith only [h1542, h2, hlam]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    rcases p1540_3 (m.d 0 5) (by simp) with h1551 | h1551
                                    · rcases p1540_3 (m.d 1 5) (by simp) with h1552 | h1552
                                      · linarith only [h1552, h2, hlam]
                                      · linarith only [h10, h1552, hlam]
                                    · linarith only [h1551, h5, hlam]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1489_1, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h11, h3, h416, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h2, hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h355, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h416, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h5, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h10, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h1336, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h1338, hlam, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h7, hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h11, h1340, h3, h416, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h8, hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h11, h416, h9, hc23, hc45, hlam, hphi, ht34, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1540_1]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [h1340, hlam, p1540_0]
                                  · have p1540_0 := h1540c.1
                                    have p1540_1 := h1540c.2.1
                                    have p1540_2 := h1540c.2.2.1
                                    have p1540_3 := h1540c.2.2.2
                                    linarith only [hlam, p1540_0]
                                · linarith only [h1539, hlam, p1489_0]
                              · linarith only [h11, h1538, hlam]
                        · linarith only [h1, h1533, hlam]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        rcases p1489_3 (m.d 0 3) (by simp) with h1581 | h1581
                        · rcases p1489_3 (m.d 1 3) (by simp) with h1582 | h1582
                          · linarith only [h1582, h355, hlam]
                          · linarith only [h1582, h9, hlam]
                        · linarith only [h1581, h3, hlam]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [h1340, hlam, p1489_0]
                      · have p1489_0 := h1489c.1
                        have p1489_1 := h1489c.2.1
                        have p1489_2 := h1489c.2.2.1
                        have p1489_3 := h1489c.2.2.2
                        linarith only [hlam, p1489_0]
              · linarith only [h1482, hlam, p1341_0]
            · linarith only [h1481, h5, hlam]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h3, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h9, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h1334, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h1336, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h4, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h0, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1341_1]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h0, h10, h1338, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1341_1]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h1338, hlam, p1341_1]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h5, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h10, hlam, p1341_0]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h0, h10, h1340, h3, h416, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1341_1]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [h0, h10, h1340, h3, h416, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1341_1]
          · have p1341_0 := h1341c.1
            have p1341_1 := h1341c.2.1
            have p1341_2 := h1341c.2.2.1
            have p1341_3 := h1341c.2.2.2
            linarith only [hlam, p1341_0]
        · rcases h2bigk with h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1607 | h1607
            · rcases p1605_3 (m.d 1 2) (by simp) with h1608 | h1608
              · linarith only [h0, h1608, hlam]
              · rcases p1605_3 (m.d 2 3) (by simp) with h1610 | h1610
                · linarith only [h1610, h3, hlam]
                · rcases p1605_3 (m.d 2 4) (by simp) with h1612 | h1612
                  · linarith only [h1612, h4, hlam]
                  · rcases p1605_3 (m.d 2 5) (by simp) with h1614 | h1614
                    · linarith only [h1614, h5, hlam]
                    · rcases h3bigk with h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h11, h1340, h6, h8, hlam, p1616_2]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h11, h1340, h6, h8, h9, hlam, p1616_2]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        rcases p1616_3 (m.d 0 3) (by simp) with h1620 | h1620
                        · rcases p1616_3 (m.d 1 3) (by simp) with h1621 | h1621
                          · linarith only [h1, h1621, hlam]
                          · rcases p1616_3 (m.d 2 3) (by simp) with h1623 | h1623
                            · linarith only [h1623, h3, hlam]
                            · rcases p1616_3 (m.d 3 4) (by simp) with h1625 | h1625
                              · linarith only [h1625, hlam, p1616_0]
                              · rcases p1616_3 (m.d 3 5) (by simp) with h1627 | h1627
                                · linarith only [h1627, h7, hlam]
                                · linarith only [h1340, h1627, hlam]
                        · linarith only [h1620, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        rcases p1616_3 (m.d 0 3) (by simp) with h1631 | h1631
                        · rcases p1616_3 (m.d 1 3) (by simp) with h1632 | h1632
                          · linarith only [h1, h1632, hlam]
                          · rcases p1616_3 (m.d 2 3) (by simp) with h1634 | h1634
                            · linarith only [h1634, h3, hlam]
                            · rcases p1616_3 (m.d 3 4) (by simp) with h1636 | h1636
                              · linarith only [h1636, h6, hlam]
                              · rcases p1616_3 (m.d 3 5) (by simp) with h1638 | h1638
                                · linarith only [h1638, hlam, p1616_0]
                                · rcases h5bigk with h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    rcases p1640_3 (m.d 0 5) (by simp) with h1642 | h1642
                                    · rcases p1640_3 (m.d 1 5) (by simp) with h1643 | h1643
                                      · linarith only [h1643, h2, hlam]
                                      · rcases p1640_3 (m.d 2 5) (by simp) with h1645 | h1645
                                        · linarith only [h1645, h5, hlam]
                                        · rcases p1640_3 (m.d 3 5) (by simp) with h1647 | h1647
                                          · linarith only [h1647, h7, hlam]
                                          · linarith only [h1647, h355, hlam]
                                    · linarith only [h1642, h2, hlam]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    rcases p1640_3 (m.d 0 5) (by simp) with h1651 | h1651
                                    · rcases p1640_3 (m.d 1 5) (by simp) with h1652 | h1652
                                      · linarith only [h1652, h2, hlam]
                                      · linarith only [h10, h1652, hlam]
                                    · linarith only [h1651, h5, hlam]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h6, h8, hlam, p1616_2, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h0, h1340, h3, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h2, hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h1334, h1338, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h355, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h416, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h5, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h10, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h1336, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h1338, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h7, hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p1616_1, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1616_1, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h1340, hlam, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h8, hlam, p1640_0]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h10, h1334, h1338, hc23, hc45, hlam, hphi, ht34, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p1640_1]
                                  · have p1640_0 := h1640c.1
                                    have p1640_1 := h1640c.2.1
                                    have p1640_2 := h1640c.2.2.1
                                    have p1640_3 := h1640c.2.2.2
                                    linarith only [hlam, p1640_0]
                        · linarith only [h1631, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h1, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h11, hc23, hc34, hlam, hphi, p1616_1]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h11, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h355, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h3, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h9, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h1334, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h1336, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h6, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h0, h1340, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1616_1]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h0, h1340, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1616_1]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h1340, hlam, p1616_1]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h7, hlam, p1616_0]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        rcases p1616_3 (m.d 0 3) (by simp) with h1695 | h1695
                        · rcases p1616_3 (m.d 1 3) (by simp) with h1696 | h1696
                          · linarith only [h1696, hlam, p1616_0]
                          · rcases p1616_3 (m.d 2 3) (by simp) with h1698 | h1698
                            · linarith only [h1336, h1698, hlam]
                            · rcases p1616_3 (m.d 3 4) (by simp) with h1700 | h1700
                              · linarith only [h1340, h1700, hlam]
                              · linarith only [h11, h1700, hlam]
                        · linarith only [h1, h1695, hlam]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        rcases p1616_3 (m.d 0 3) (by simp) with h1704 | h1704
                        · rcases p1616_3 (m.d 1 3) (by simp) with h1705 | h1705
                          · linarith only [h1705, h355, hlam]
                          · linarith only [h1705, h9, hlam]
                        · linarith only [h1704, h3, hlam]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [h11, h9, hc23, hc35, hlam, hphi, p1616_1]
                      · have p1616_0 := h1616c.1
                        have p1616_1 := h1616c.2.1
                        have p1616_2 := h1616c.2.2.1
                        have p1616_3 := h1616c.2.2.2
                        linarith only [hlam, p1616_0]
            · linarith only [h0, h1607, hlam]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h11, h1340, h3, h6, h8, h9, hlam, p1605_2]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1713 | h1713
            · rcases p1605_3 (m.d 1 2) (by simp) with h1714 | h1714
              · linarith only [h0, h1714, hlam]
              · linarith only [h10, h1338, h1714, hlam]
            · linarith only [h1713, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1718 | h1718
            · rcases p1605_3 (m.d 1 2) (by simp) with h1719 | h1719
              · linarith only [h0, h1719, hlam]
              · linarith only [h10, h1719, hlam]
            · linarith only [h1718, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h0, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1725 | h1725
            · rcases p1605_3 (m.d 1 2) (by simp) with h1726 | h1726
              · rcases p1605_3 (m.d 2 3) (by simp) with h1727 | h1727
                · linarith only [h1727, hlam, p1605_0]
                · rcases p1605_3 (m.d 2 4) (by simp) with h1729 | h1729
                  · linarith only [h10, h1338, h1729, hlam]
                  · linarith only [h1334, h1729, hlam]
              · linarith only [h1726, hlam, p1605_0]
            · linarith only [h1725, h3, hlam]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1734 | h1734
            · rcases p1605_3 (m.d 1 2) (by simp) with h1735 | h1735
              · rcases p1605_3 (m.d 2 3) (by simp) with h1736 | h1736
                · linarith only [h1736, h9, hlam]
                · rcases p1605_3 (m.d 2 4) (by simp) with h1738 | h1738
                  · linarith only [h1738, hlam, p1605_0]
                  · rcases p1605_3 (m.d 2 5) (by simp) with h1740 | h1740
                    · linarith only [h10, h1740, hlam]
                    · linarith only [h1338, h1740, hlam]
              · linarith only [h1735, hlam, p1605_0]
            · linarith only [h1734, h4, hlam]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            rcases p1605_3 (m.d 0 2) (by simp) with h1745 | h1745
            · rcases p1605_3 (m.d 1 2) (by simp) with h1746 | h1746
              · rcases p1605_3 (m.d 2 3) (by simp) with h1747 | h1747
                · linarith only [h1747, h9, hlam]
                · rcases p1605_3 (m.d 2 4) (by simp) with h1749 | h1749
                  · linarith only [h1338, h1749, hlam, p1605_1]
                  · rcases p1605_3 (m.d 2 5) (by simp) with h1751 | h1751
                    · linarith only [h1751, hlam, p1605_0]
                    · rcases h3bigk with h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h11, h1340, h6, h8, hlam, p1753_2]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h11, h1340, h6, h8, h9, hlam, p1753_2]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        rcases p1753_3 (m.d 0 3) (by simp) with h1757 | h1757
                        · rcases p1753_3 (m.d 1 3) (by simp) with h1758 | h1758
                          · linarith only [h1, h1758, hlam]
                          · rcases p1753_3 (m.d 2 3) (by simp) with h1760 | h1760
                            · linarith only [h1760, h3, hlam]
                            · rcases p1753_3 (m.d 3 4) (by simp) with h1762 | h1762
                              · linarith only [h1762, hlam, p1753_0]
                              · rcases p1753_3 (m.d 3 5) (by simp) with h1764 | h1764
                                · linarith only [h1764, h7, hlam]
                                · linarith only [h1340, h1764, hlam]
                        · linarith only [h1757, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        rcases p1753_3 (m.d 0 3) (by simp) with h1768 | h1768
                        · rcases p1753_3 (m.d 1 3) (by simp) with h1769 | h1769
                          · linarith only [h1, h1769, hlam]
                          · rcases p1753_3 (m.d 2 3) (by simp) with h1771 | h1771
                            · linarith only [h1771, h3, hlam]
                            · rcases p1753_3 (m.d 3 4) (by simp) with h1773 | h1773
                              · linarith only [h1773, h6, hlam]
                              · rcases p1753_3 (m.d 3 5) (by simp) with h1775 | h1775
                                · linarith only [h1775, hlam, p1753_0]
                                · rcases h5bigk with h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    rcases p1777_3 (m.d 0 5) (by simp) with h1779 | h1779
                                    · rcases p1777_3 (m.d 1 5) (by simp) with h1780 | h1780
                                      · linarith only [h1780, h2, hlam]
                                      · rcases p1777_3 (m.d 2 5) (by simp) with h1782 | h1782
                                        · linarith only [h1782, h5, hlam]
                                        · rcases p1777_3 (m.d 3 5) (by simp) with h1784 | h1784
                                          · linarith only [h1784, h7, hlam]
                                          · linarith only [h1784, h355, hlam]
                                    · linarith only [h1779, h2, hlam]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    rcases p1777_3 (m.d 0 5) (by simp) with h1788 | h1788
                                    · rcases p1777_3 (m.d 1 5) (by simp) with h1789 | h1789
                                      · linarith only [h1789, h2, hlam]
                                      · linarith only [h10, h1789, hlam]
                                    · linarith only [h1788, h5, hlam]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h6, h8, hlam, p1753_2, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h1340, h3, h6, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h2, hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h1338, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h355, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h416, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h5, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h10, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h1336, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h1338, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h7, hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h0, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p1753_1, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h1340, hlam, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h8, hlam, p1777_0]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h11, h416, h9, hc23, hc45, hlam, hphi, ht34, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h0, h1334, h1338, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p1777_1]
                                  · have p1777_0 := h1777c.1
                                    have p1777_1 := h1777c.2.1
                                    have p1777_2 := h1777c.2.2.1
                                    have p1777_3 := h1777c.2.2.2
                                    linarith only [hlam, p1777_0]
                        · linarith only [h1768, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h11, hc23, hc34, hlam, hphi, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h11, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h355, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h3, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h9, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1334, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1336, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h6, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h1340, h3, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h1340, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1340, hlam, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h7, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        rcases p1753_3 (m.d 0 3) (by simp) with h1832 | h1832
                        · rcases p1753_3 (m.d 1 3) (by simp) with h1833 | h1833
                          · linarith only [h1833, hlam, p1753_0]
                          · rcases p1753_3 (m.d 2 3) (by simp) with h1835 | h1835
                            · linarith only [h1336, h1835, hlam]
                            · rcases p1753_3 (m.d 3 4) (by simp) with h1837 | h1837
                              · linarith only [h1340, h1837, hlam]
                              · linarith only [h11, h1837, hlam]
                        · linarith only [h1, h1832, hlam]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        rcases p1753_3 (m.d 0 3) (by simp) with h1841 | h1841
                        · rcases p1753_3 (m.d 1 3) (by simp) with h1842 | h1842
                          · linarith only [h1842, h355, hlam]
                          · linarith only [h1842, h9, hlam]
                        · linarith only [h1841, h3, hlam]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h11, h3, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
              · linarith only [h1746, hlam, p1605_0]
            · linarith only [h1745, h5, hlam]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h3, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h9, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h1334, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h1336, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h4, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h0, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h0, h1338, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h1338, hlam, p1605_1]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h5, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h10, hlam, p1605_0]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1605_1]
          · have p1605_0 := h1605c.1
            have p1605_1 := h1605c.2.1
            have p1605_2 := h1605c.2.2.1
            have p1605_3 := h1605c.2.2.2
            linarith only [hlam, p1605_0]

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355 h416

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h355 | h355
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h355

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h1865 | h1865
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1866 | h1866
    · linarith only [h10, h1866, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1868 | h1868
      · linarith only [h10, h1865, h1868, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1870 | h1870
        · linarith only [h0, h10, h1870, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1865, h1866, h1870, h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1873 | h1873
    · linarith only [h10, h1873, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1875 | h1875
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1876 | h1876
        · linarith only [h0, h1865, h1876, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1878 | h1878
          · linarith only [h0, h10, h1878, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1880 | h1880
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1881 | h1881
              · rcases h2bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  rcases p1882_3 (m.d 0 2) (by simp) with h1884 | h1884
                  · rcases p1882_3 (m.d 1 2) (by simp) with h1885 | h1885
                    · linarith only [h0, h1885, hlam]
                    · rcases p1882_3 (m.d 2 3) (by simp) with h1887 | h1887
                      · linarith only [h1887, h3, hlam]
                      · rcases p1882_3 (m.d 2 4) (by simp) with h1889 | h1889
                        · linarith only [h1889, h4, hlam]
                        · linarith only [h10, h1880, h1889, hlam]
                  · linarith only [h0, h1884, hlam]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h10, h1876, h1880, h3, h6, h9, hlam, p1882_2]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h0, h10, h1880, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h0, h10, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h0, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h10, h1876, h1880, h6, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h10, h1880, hlam, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h10, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h3, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h9, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h1876, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h1878, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h4, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h0, h1876, h3, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  rcases p1882_3 (m.d 0 2) (by simp) with h1908 | h1908
                  · rcases p1882_3 (m.d 1 2) (by simp) with h1909 | h1909
                    · linarith only [h10, h1880, h1909, hlam]
                    · linarith only [h1909, h9, hlam]
                  · linarith only [h1908, h3, hlam]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h0, h10, h1876, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h5, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h1878, h9, hc23, hc35, hlam, hphi, p1882_1]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  rcases p1882_3 (m.d 0 2) (by simp) with h1917 | h1917
                  · rcases p1882_3 (m.d 1 2) (by simp) with h1918 | h1918
                    · linarith only [h10, h1918, hlam]
                    · linarith only [h1918, h9, hlam]
                  · linarith only [h1917, h3, hlam]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [h1880, hlam, p1882_0]
                · have p1882_0 := h1882c.1
                  have p1882_1 := h1882c.2.1
                  have p1882_2 := h1882c.2.2.1
                  have p1882_3 := h1882c.2.2.2
                  linarith only [hlam, p1882_0]
              · linarith only [h0, h10, h1876, h1880, h1881, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h10, h1875, h1880, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1926 | h1926
        · linarith only [h0, h10, h1926, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1928 | h1928
          · linarith only [h0, h10, h1928, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1930 | h1930
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1931 | h1931
              · rcases h2bigk with h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  rcases p1932_3 (m.d 0 2) (by simp) with h1934 | h1934
                  · rcases p1932_3 (m.d 1 2) (by simp) with h1935 | h1935
                    · linarith only [h0, h1935, hlam]
                    · rcases p1932_3 (m.d 2 3) (by simp) with h1937 | h1937
                      · linarith only [h1937, h3, hlam]
                      · rcases p1932_3 (m.d 2 4) (by simp) with h1939 | h1939
                        · linarith only [h1939, h4, hlam]
                        · linarith only [h10, h1875, h1930, h1939, hlam]
                  · linarith only [h0, h1934, hlam]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h1865, h1875, h1926, h1930, h3, h6, h9, hlam, p1932_2]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, h1865, h1875, h1930, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, h10, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h10, h1875, h1930, hlam, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h10, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h3, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h9, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h1926, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h1928, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h4, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h1926, h9, hc23, hc34, hlam, hphi, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  rcases p1932_3 (m.d 0 2) (by simp) with h1958 | h1958
                  · rcases p1932_3 (m.d 1 2) (by simp) with h1959 | h1959
                    · linarith only [h0, h10, h1928, h1931, h1959, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1932_1]
                    · linarith only [h1959, h9, hlam]
                  · linarith only [h1958, h3, hlam]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h5, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h0, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1932_1]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  rcases p1932_3 (m.d 0 2) (by simp) with h1967 | h1967
                  · rcases p1932_3 (m.d 1 2) (by simp) with h1968 | h1968
                    · linarith only [h10, h1968, hlam]
                    · linarith only [h1968, h9, hlam]
                  · linarith only [h1967, h3, hlam]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [h1930, hlam, p1932_0]
                · have p1932_0 := h1932c.1
                  have p1932_1 := h1932c.2.1
                  have p1932_2 := h1932c.2.2.1
                  have p1932_3 := h1932c.2.2.2
                  linarith only [hlam, p1932_0]
              · linarith only [h1926, h1930, h1931, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1975 | h1975
              · linarith only [h0, h10, h1930, h1975, h3, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases h2bigk with h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  rcases p1977_3 (m.d 0 2) (by simp) with h1979 | h1979
                  · rcases p1977_3 (m.d 1 2) (by simp) with h1980 | h1980
                    · linarith only [h0, h1980, hlam]
                    · rcases p1977_3 (m.d 2 3) (by simp) with h1982 | h1982
                      · linarith only [h1982, h3, hlam]
                      · rcases p1977_3 (m.d 2 4) (by simp) with h1984 | h1984
                        · linarith only [h1984, h4, hlam]
                        · rcases p1977_3 (m.d 2 5) (by simp) with h1986 | h1986
                          · linarith only [h1986, h5, hlam]
                          · linarith only [h10, h1986, hlam]
                  · linarith only [h0, h1979, hlam]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h10, h5, h9, hlam, p1977_2]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  rcases p1977_3 (m.d 0 2) (by simp) with h1991 | h1991
                  · rcases p1977_3 (m.d 1 2) (by simp) with h1992 | h1992
                    · linarith only [h0, h1992, hlam]
                    · rcases p1977_3 (m.d 2 3) (by simp) with h1994 | h1994
                      · linarith only [h1994, h3, hlam]
                      · rcases p1977_3 (m.d 2 4) (by simp) with h1996 | h1996
                        · linarith only [h1996, hlam, p1977_0]
                        · rcases p1977_3 (m.d 2 5) (by simp) with h1998 | h1998
                          · linarith only [h1998, h5, hlam]
                          · linarith only [h1930, h1998, hlam]
                  · linarith only [h1991, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h10, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h10, h1928, h1975, h6, h8, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h10, h1928, h1975, h3, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h10, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h3, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h9, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1926, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1928, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h4, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h1926, h1975, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1930, hlam, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h5, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h1928, h1975, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  rcases p1977_3 (m.d 0 2) (by simp) with h2020 | h2020
                  · rcases p1977_3 (m.d 1 2) (by simp) with h2021 | h2021
                    · linarith only [h10, h2021, hlam]
                    · linarith only [h2021, h9, hlam]
                  · linarith only [h2020, h3, hlam]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  rcases p1977_3 (m.d 0 2) (by simp) with h2025 | h2025
                  · rcases p1977_3 (m.d 1 2) (by simp) with h2026 | h2026
                    · linarith only [h10, h2026, hlam]
                    · linarith only [h0, h1928, h1975, h2026, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
                  · linarith only [h2025, h4, hlam]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10

end R2N4
