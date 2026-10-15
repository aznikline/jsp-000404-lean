import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6208000 in
set_option maxHeartbeats 6208000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  rcases m.htr 0 1 5 (by decide) (by decide) with h1407 | h1407
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1408 | h1408
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1409 | h1409
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1410 | h1410
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1411 | h1411
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1412 | h1412
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1413 | h1413
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1414 | h1414
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1415 | h1415
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1417 | h1417
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1418 | h1418
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1419 | h1419
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1420 | h1420
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1422 | h1422
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1423 | h1423
                                  · rcases h2bigk with h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h0, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1420, h1423, hc02, hc45, hlam, hphi, ht0b, ht5b, p1424_1]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      rcases p1424_3 (m.d 0 2) (by simp) with h1428 | h1428
                                      · rcases p1424_3 (m.d 1 2) (by simp) with h1429 | h1429
                                        · rcases p1424_3 (m.d 2 3) (by simp) with h1430 | h1430
                                          · linarith only [h1408, h1430, hlam]
                                          · linarith only [h1420, h1430, hlam]
                                        · linarith only [h1415, h1429, hlam]
                                      · linarith only [h1428, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      rcases p1424_3 (m.d 0 2) (by simp) with h1435 | h1435
                                      · rcases p1424_3 (m.d 1 2) (by simp) with h1436 | h1436
                                        · rcases p1424_3 (m.d 2 3) (by simp) with h1437 | h1437
                                          · linarith only [h1408, h1437, hlam]
                                          · linarith only [h1421, h1437, hlam]
                                        · linarith only [h1416, h1436, hlam]
                                      · linarith only [h1435, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h0, h1407, h1416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1424_1, u2ehi4]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1420, h1423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1424_1]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      rcases p1424_3 (m.d 0 2) (by simp) with h1445 | h1445
                                      · linarith only [h0, h1445, hlam]
                                      · linarith only [h1409, h1445, hlam]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      rcases p1424_3 (m.d 0 2) (by simp) with h1448 | h1448
                                      · linarith only [h0, h1448, hlam]
                                      · linarith only [h1410, h1448, hlam]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1408, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1414, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1408, h1422, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1424_1, u2ehi4]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h0, h1408, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1424_1, u2ehi4]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1409, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1415, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1420, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hc24, hlam, hphi, p1424_1, u2ehi4]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1410, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1416, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1421, hlam, p1424_0]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [h1422, hlam, p1424_1]
                                    · have p1424_0 := h1424c.1
                                      have p1424_1 := h1424c.2.1
                                      have p1424_2 := h1424c.2.2.1
                                      have p1424_3 := h1424c.2.2.2
                                      linarith only [hlam, p1424_0]
                                  · rcases h2bigk with h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c | h1466c
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h0, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h0, h1420, h1422, h1423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h0, h1422, h1423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      rcases p1466_3 (m.d 0 2) (by simp) with h1471 | h1471
                                      · rcases p1466_3 (m.d 1 2) (by simp) with h1472 | h1472
                                        · rcases p1466_3 (m.d 2 3) (by simp) with h1473 | h1473
                                          · linarith only [h1408, h1473, hlam]
                                          · linarith only [h1421, h1473, hlam]
                                        · linarith only [h1416, h1472, hlam]
                                      · linarith only [h1471, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h0, h1407, h1416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi4]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1420, h1422, h1423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1422, h1423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      rcases p1466_3 (m.d 0 2) (by simp) with h1482 | h1482
                                      · linarith only [h0, h1482, hlam]
                                      · linarith only [h1410, h1482, hlam]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1408, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1414, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1408, h1422, h1423, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h0, h1408, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1466_1, u2ehi4]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1409, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1415, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1420, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hc24, hlam, hphi, p1466_1, u2ehi4]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1410, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1416, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1421, hlam, p1466_0]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [h1422, hlam, p1466_1]
                                    · have p1466_0 := h1466c.1
                                      have p1466_1 := h1466c.2.1
                                      have p1466_2 := h1466c.2.2.1
                                      have p1466_3 := h1466c.2.2.2
                                      linarith only [hlam, p1466_0]
                                · linarith only [h0, h1407, h1419, h1422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h1407, h1414, h1418, h1421, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1502 | h1502
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1503 | h1503
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1504 | h1504
                                  · rcases h2bigk with h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h0, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1508 | h1508
                                      · rcases p1505_3 (m.d 1 2) (by simp) with h1509 | h1509
                                        · rcases p1505_3 (m.d 2 3) (by simp) with h1510 | h1510
                                          · linarith only [h1510, hlam, p1505_0]
                                          · rcases p1505_3 (m.d 2 4) (by simp) with h1512 | h1512
                                            · linarith only [h1409, h1512, hlam]
                                            · linarith only [h1420, h1512, hlam]
                                        · linarith only [h1414, h1509, hlam]
                                      · linarith only [h1508, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1517 | h1517
                                      · rcases p1505_3 (m.d 1 2) (by simp) with h1518 | h1518
                                        · rcases p1505_3 (m.d 2 3) (by simp) with h1519 | h1519
                                          · linarith only [h1408, h1519, hlam]
                                          · rcases p1505_3 (m.d 2 4) (by simp) with h1521 | h1521
                                            · linarith only [h1521, hlam, p1505_0]
                                            · rcases p1505_3 (m.d 2 5) (by simp) with h1523 | h1523
                                              · linarith only [h1410, h1523, hlam]
                                              · rcases h3bigk with h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h879, hlam, p1525_1]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  rcases p1525_3 (m.d 0 3) (by simp) with h1528 | h1528
                                                  · rcases p1525_3 (m.d 1 3) (by simp) with h1529 | h1529
                                                    · rcases p1525_3 (m.d 2 3) (by simp) with h1530 | h1530
                                                      · linarith only [h1408, h1530, hlam]
                                                      · rcases p1525_3 (m.d 3 4) (by simp) with h1532 | h1532
                                                        · linarith only [h1411, h1532, hlam]
                                                        · linarith only [h1420, h1532, hlam]
                                                    · linarith only [h1414, h1529, hlam]
                                                  · linarith only [h1408, h1528, hlam]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1414, h1420, h1502, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u2ehi4]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, h1420, h1502, hlam, p1525_2]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, h1414, h1420, h1502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u2ehi4]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  rcases p1525_3 (m.d 0 3) (by simp) with h1541 | h1541
                                                  · linarith only [h1541, h879, hlam]
                                                  · linarith only [h1408, h1541, hlam]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1414, h1420, h1502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u2ehi4]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, h1420, h1502, h879, hlam, p1525_2]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1408, hlam, p1525_1]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1414, hlam, p1525_1]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1420, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, h1420, hc03, hc35, hlam, hphi, ht0b, ht5b, p1525_1]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1417, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1411, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u2ehi2]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  rcases p1525_3 (m.d 0 3) (by simp) with h1555 | h1555
                                                  · rcases p1525_3 (m.d 1 3) (by simp) with h1556 | h1556
                                                    · rcases p1525_3 (m.d 2 3) (by simp) with h1557 | h1557
                                                      · linarith only [h1420, h1557, hlam]
                                                      · linarith only [h1502, h1557, hlam]
                                                    · linarith only [h1418, h1556, hlam]
                                                  · linarith only [h1412, h1555, hlam]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1412, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1418, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1502, hlam, p1525_0]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [h1504, hlam, p1525_1]
                                                · have p1525_0 := h1525c.1
                                                  have p1525_1 := h1525c.2.1
                                                  have p1525_2 := h1525c.2.2.1
                                                  have p1525_3 := h1525c.2.2.2
                                                  linarith only [hlam, p1525_0]
                                        · linarith only [h1415, h1518, hlam]
                                      · linarith only [h1517, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1569 | h1569
                                      · rcases p1505_3 (m.d 1 2) (by simp) with h1570 | h1570
                                        · rcases p1505_3 (m.d 2 3) (by simp) with h1571 | h1571
                                          · linarith only [h1408, h1571, hlam]
                                          · linarith only [h1502, h1571, hlam]
                                        · linarith only [h1416, h1570, hlam]
                                      · linarith only [h1569, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h0, h1407, h1416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1505_1, u2ehi4]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1578 | h1578
                                      · linarith only [h0, h1578, hlam]
                                      · linarith only [h1408, h1578, hlam]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1581 | h1581
                                      · linarith only [h0, h1581, hlam]
                                      · linarith only [h1409, h1581, hlam]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      rcases p1505_3 (m.d 0 2) (by simp) with h1584 | h1584
                                      · linarith only [h0, h1584, hlam]
                                      · linarith only [h1410, h1584, hlam]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1408, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1414, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1420, hlam, p1505_1]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1408, h1411, h1420, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1, u2ehi4]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1409, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1415, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hc24, hlam, hphi, p1505_1, u2ehi2]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h0, h1408, h1411, h1420, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1505_1, u2ehi4]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1410, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1416, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1502, hlam, p1505_0]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [h1503, hlam, p1505_1]
                                    · have p1505_0 := h1505c.1
                                      have p1505_1 := h1505c.2.1
                                      have p1505_2 := h1505c.2.2.1
                                      have p1505_3 := h1505c.2.2.2
                                      linarith only [hlam, p1505_0]
                                  · linarith only [h0, h1407, h1419, h1420, h1504, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h1407, h1414, h1419, h1503, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h1407, h1414, h1418, h1502, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1605 | h1605
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1606 | h1606
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1607 | h1607
                                · linarith only [h1415, h1419, h1607, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1609 | h1609
                                  · linarith only [h1415, h1419, h1605, h1609, hlam]
                                  · rcases h2bigk with h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h0, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1614 | h1614
                                      · rcases p1611_3 (m.d 1 2) (by simp) with h1615 | h1615
                                        · rcases p1611_3 (m.d 2 3) (by simp) with h1616 | h1616
                                          · linarith only [h1616, hlam, p1611_0]
                                          · rcases p1611_3 (m.d 2 4) (by simp) with h1618 | h1618
                                            · linarith only [h1409, h1618, hlam]
                                            · rcases p1611_3 (m.d 2 5) (by simp) with h1620 | h1620
                                              · linarith only [h1410, h1620, hlam]
                                              · rcases h3bigk with h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h879, hlam, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1625 | h1625
                                                  · rcases p1622_3 (m.d 1 3) (by simp) with h1626 | h1626
                                                    · rcases p1622_3 (m.d 2 3) (by simp) with h1627 | h1627
                                                      · linarith only [h1408, h1627, hlam]
                                                      · rcases p1622_3 (m.d 3 4) (by simp) with h1629 | h1629
                                                        · linarith only [h1411, h1629, hlam]
                                                        · rcases p1622_3 (m.d 3 5) (by simp) with h1631 | h1631
                                                          · linarith only [h1412, h1631, hlam]
                                                          · rcases h3emax with h1633 | h1633 | h1633 | h1633 | h1633
                                                            · linarith only [h1411, h1413, h1415, h1419, h1633, hlam, ht23, u2ehi3]
                                                            · linarith only [h0, h1408, h1411, h1413, h1415, h1419, h1633, h879, hc01, hc12, hlam, hphi, ht23, u2ehi3]
                                                            · linarith only [h1633, hlam, ht23, u2ehi2]
                                                            · rcases h5bigk with h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h0, h1407, h1416, h1607, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi3]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h0, h1407, h1607, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi3]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                rcases p1637_3 (m.d 0 5) (by simp) with h1641 | h1641
                                                                · rcases p1637_3 (m.d 1 5) (by simp) with h1642 | h1642
                                                                  · linarith only [h1407, h1642, hlam]
                                                                  · linarith only [h1418, h1642, hlam]
                                                                · linarith only [h1412, h1641, hlam]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1407, h1414, h1415, h1419, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi3]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1407, hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1407, h1414, h1607, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi3]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1407, h1414, h1609, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1419, hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1410, hlam, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1416, hlam, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1606, h1609, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1611_1, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1607, hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1412, hlam, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1418, hlam, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1606, hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1609, hlam, p1637_0]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1413, hlam, p1637_1]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1413, h1416, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi4]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [h1411, h1413, h1414, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1637_1, u2ehi4]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                rcases p1637_3 (m.d 0 5) (by simp) with h1665 | h1665
                                                                · rcases p1637_3 (m.d 1 5) (by simp) with h1666 | h1666
                                                                  · linarith only [h1419, h1666, hlam]
                                                                  · linarith only [h1418, h1666, hlam]
                                                                · linarith only [h1412, h1665, hlam]
                                                              · have p1637_0 := h1637c.1
                                                                have p1637_1 := h1637c.2.1
                                                                have p1637_2 := h1637c.2.2.1
                                                                have p1637_3 := h1637c.2.2.2
                                                                linarith only [hlam, p1637_0]
                                                            · rcases h5bigk with h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1415, h1419, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi3]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1607, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi3]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                rcases p1671_3 (m.d 0 5) (by simp) with h1675 | h1675
                                                                · rcases p1671_3 (m.d 1 5) (by simp) with h1676 | h1676
                                                                  · linarith only [h1407, h1676, hlam]
                                                                  · linarith only [h1418, h1676, hlam]
                                                                · linarith only [h1412, h1675, hlam]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1415, h1419, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi3]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1607, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi3]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1609, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1419, hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1410, hlam, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1416, hlam, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1407, h1414, h1416, h1609, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1607, hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1412, hlam, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1418, hlam, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1606, hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1609, hlam, p1671_0]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1413, hlam, p1671_1]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1416, hc45, hlam, hphi, ht23, ht34, p1671_1, u2ehi4]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [h1411, h1413, h1414, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi4]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                rcases p1671_3 (m.d 0 5) (by simp) with h1699 | h1699
                                                                · rcases p1671_3 (m.d 1 5) (by simp) with h1700 | h1700
                                                                  · linarith only [h1419, h1700, hlam]
                                                                  · linarith only [h1418, h1700, hlam]
                                                                · linarith only [h1412, h1699, hlam]
                                                              · have p1671_0 := h1671c.1
                                                                have p1671_1 := h1671c.2.1
                                                                have p1671_2 := h1671c.2.2.1
                                                                have p1671_3 := h1671c.2.2.2
                                                                linarith only [hlam, p1671_0]
                                                    · linarith only [h1414, h1626, hlam]
                                                  · linarith only [h1408, h1625, hlam]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1707 | h1707
                                                  · rcases p1622_3 (m.d 1 3) (by simp) with h1708 | h1708
                                                    · rcases p1622_3 (m.d 2 3) (by simp) with h1709 | h1709
                                                      · linarith only [h1408, h1709, hlam]
                                                      · linarith only [h1605, h1709, hlam]
                                                    · linarith only [h1417, h1708, hlam]
                                                  · linarith only [h1707, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1714 | h1714
                                                  · rcases p1622_3 (m.d 1 3) (by simp) with h1715 | h1715
                                                    · rcases p1622_3 (m.d 2 3) (by simp) with h1716 | h1716
                                                      · linarith only [h1408, h1716, hlam]
                                                      · linarith only [h1606, h1716, hlam]
                                                    · linarith only [h1418, h1715, hlam]
                                                  · linarith only [h1714, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1407, h1414, h1415, h1419, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1622_1, u2ehi3]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1723 | h1723
                                                  · linarith only [h1723, h879, hlam]
                                                  · linarith only [h1408, h1723, hlam]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1726 | h1726
                                                  · linarith only [h1726, h879, hlam]
                                                  · linarith only [h1411, h1726, hlam]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  rcases p1622_3 (m.d 0 3) (by simp) with h1729 | h1729
                                                  · linarith only [h1729, h879, hlam]
                                                  · linarith only [h1412, h1729, hlam]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1408, hlam, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1414, hlam, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1611_1, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1611_1, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1411, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1417, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1605, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1609, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1412, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1418, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1606, hlam, p1622_0]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [h1407, h1418, h879, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1622_1]
                                                · have p1622_0 := h1622c.1
                                                  have p1622_1 := h1622c.2.1
                                                  have p1622_2 := h1622c.2.2.1
                                                  have p1622_3 := h1622c.2.2.2
                                                  linarith only [hlam, p1622_0]
                                        · linarith only [h1414, h1615, hlam]
                                      · linarith only [h1614, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1749 | h1749
                                      · rcases p1611_3 (m.d 1 2) (by simp) with h1750 | h1750
                                        · rcases p1611_3 (m.d 2 3) (by simp) with h1751 | h1751
                                          · linarith only [h1408, h1751, hlam]
                                          · linarith only [h1605, h1751, hlam]
                                        · linarith only [h1415, h1750, hlam]
                                      · linarith only [h1749, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1756 | h1756
                                      · rcases p1611_3 (m.d 1 2) (by simp) with h1757 | h1757
                                        · rcases p1611_3 (m.d 2 3) (by simp) with h1758 | h1758
                                          · linarith only [h1408, h1758, hlam]
                                          · linarith only [h1606, h1758, hlam]
                                        · linarith only [h1416, h1757, hlam]
                                      · linarith only [h1756, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h0, h1407, h1413, h1415, h1419, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1611_1, u2ehi3]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1765 | h1765
                                      · linarith only [h0, h1765, hlam]
                                      · linarith only [h1408, h1765, hlam]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1768 | h1768
                                      · linarith only [h0, h1768, hlam]
                                      · linarith only [h1409, h1768, hlam]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      rcases p1611_3 (m.d 0 2) (by simp) with h1771 | h1771
                                      · linarith only [h0, h1771, hlam]
                                      · linarith only [h1410, h1771, hlam]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1408, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1414, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hc23, hlam, hphi, p1611_1, u2ehi3]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h0, h1408, h1607, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1611_1, u2ehi3]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1409, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1415, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1605, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1607, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1410, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1416, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [h1606, hlam, p1611_0]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hc25, hlam, hphi, p1611_1, u2ehi3]
                                    · have p1611_0 := h1611c.1
                                      have p1611_1 := h1611c.2.1
                                      have p1611_2 := h1611c.2.2.1
                                      have p1611_3 := h1611c.2.2.2
                                      linarith only [hlam, p1611_0]
                              · linarith only [h0, h1407, h1418, h1606, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1413, h1417, h1419, h1605, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1407, h1416, h1418, h879, hc35, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h1407, h1416, h1417, h879, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h0, h1408, h1416, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1407, h1410, h1415, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1407, h1408, h1410, h1414, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1798 | h1798
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1799 | h1799
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1800 | h1800
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1801 | h1801
                          · linarith only [h0, h1407, h1409, h1413, h1801, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1803 | h1803
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1804 | h1804
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1805 | h1805
                                · linarith only [h1409, h1413, h1805, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1807 | h1807
                                  · linarith only [h1409, h1413, h1807, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h2bigk with h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h0, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1812 | h1812
                                      · rcases p1809_3 (m.d 1 2) (by simp) with h1813 | h1813
                                        · rcases p1809_3 (m.d 2 3) (by simp) with h1814 | h1814
                                          · linarith only [h1814, hlam, p1809_0]
                                          · rcases p1809_3 (m.d 2 4) (by simp) with h1816 | h1816
                                            · linarith only [h1409, h1816, hlam]
                                            · rcases p1809_3 (m.d 2 5) (by simp) with h1818 | h1818
                                              · linarith only [h1410, h1818, hlam]
                                              · rcases h3bigk with h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h879, hlam, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1823 | h1823
                                                  · rcases p1820_3 (m.d 1 3) (by simp) with h1824 | h1824
                                                    · rcases p1820_3 (m.d 2 3) (by simp) with h1825 | h1825
                                                      · linarith only [h1408, h1825, hlam]
                                                      · rcases p1820_3 (m.d 3 4) (by simp) with h1827 | h1827
                                                        · linarith only [h1411, h1827, hlam]
                                                        · rcases p1820_3 (m.d 3 5) (by simp) with h1829 | h1829
                                                          · linarith only [h1412, h1829, hlam]
                                                          · rcases h3emax with h1831 | h1831 | h1831 | h1831 | h1831
                                                            · linarith only [h1831, hc23, hlam, p1820_1]
                                                            · linarith only [h1831, h879, hc01, hlam, ht12, ht23]
                                                            · linarith only [h1831, hlam, ht23, u2ehi2]
                                                            · rcases h5bigk with h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, h1796, h1798, h1805, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1835_1, u2ehi3]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, h1796, h1805, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1835_1, u2ehi3]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                rcases p1835_3 (m.d 0 5) (by simp) with h1839 | h1839
                                                                · rcases p1835_3 (m.d 1 5) (by simp) with h1840 | h1840
                                                                  · linarith only [h1407, h1840, hlam]
                                                                  · linarith only [h1800, h1840, hlam]
                                                                · linarith only [h1412, h1839, hlam]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1413, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, h1796, h1805, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1835_1, u2ehi3]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, h1796, h1807, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1801, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1410, hlam, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1798, hlam, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1407, h1796, h1798, h1807, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1805, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1412, hlam, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1800, hlam, p1835_1]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1804, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1807, hlam, p1835_0]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1410, hc45, hlam, hphi, ht23, ht34, p1835_1, u2ehi4]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [h1797, h1801, hc45, hlam, hphi, ht23, ht34, p1835_1, u2ehi3]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hc45, hlam, hphi, ht23, ht34, p1835_1, u2ehi4]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                rcases p1835_3 (m.d 0 5) (by simp) with h1863 | h1863
                                                                · linarith only [h1413, h1863, hlam]
                                                                · linarith only [h1412, h1863, hlam]
                                                              · have p1835_0 := h1835c.1
                                                                have p1835_1 := h1835c.2.1
                                                                have p1835_2 := h1835c.2.2.1
                                                                have p1835_3 := h1835c.2.2.2
                                                                linarith only [hlam, p1835_0]
                                                            · rcases h5bigk with h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, h1796, h1797, h1801, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1867_1, u2ehi3]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, h1796, h1805, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1867_1, u2ehi3]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                rcases p1867_3 (m.d 0 5) (by simp) with h1871 | h1871
                                                                · rcases p1867_3 (m.d 1 5) (by simp) with h1872 | h1872
                                                                  · linarith only [h1407, h1872, hlam]
                                                                  · linarith only [h1800, h1872, hlam]
                                                                · linarith only [h1412, h1871, hlam]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1413, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, h1796, h1805, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1867_1, u2ehi3]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, h1796, h1807, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1801, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1410, hlam, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1798, hlam, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1407, h1796, h1798, h1807, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1805, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1412, hlam, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1800, hlam, p1867_1]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1804, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1807, hlam, p1867_0]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1410, hc45, hlam, hphi, ht23, ht34, p1867_1, u2ehi4]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [h1798, hc45, hlam, hphi, ht23, ht34, p1867_1, u2ehi4]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hc45, hlam, hphi, ht23, ht34, p1867_1, u2ehi4]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                rcases p1867_3 (m.d 0 5) (by simp) with h1895 | h1895
                                                                · linarith only [h1413, h1895, hlam]
                                                                · linarith only [h1412, h1895, hlam]
                                                              · have p1867_0 := h1867c.1
                                                                have p1867_1 := h1867c.2.1
                                                                have p1867_2 := h1867c.2.2.1
                                                                have p1867_3 := h1867c.2.2.2
                                                                linarith only [hlam, p1867_0]
                                                    · linarith only [h1796, h1824, hlam]
                                                  · linarith only [h1408, h1823, hlam]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1901 | h1901
                                                  · rcases p1820_3 (m.d 1 3) (by simp) with h1902 | h1902
                                                    · rcases p1820_3 (m.d 2 3) (by simp) with h1903 | h1903
                                                      · linarith only [h1408, h1903, hlam]
                                                      · linarith only [h1803, h1903, hlam]
                                                    · linarith only [h1799, h1902, hlam]
                                                  · linarith only [h1901, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1908 | h1908
                                                  · rcases p1820_3 (m.d 1 3) (by simp) with h1909 | h1909
                                                    · rcases p1820_3 (m.d 2 3) (by simp) with h1910 | h1910
                                                      · linarith only [h1408, h1910, hlam]
                                                      · linarith only [h1804, h1910, hlam]
                                                    · linarith only [h1800, h1909, hlam]
                                                  · linarith only [h1908, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1407, h1796, h1797, h1801, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1820_1, u2ehi3]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1917 | h1917
                                                  · linarith only [h1917, h879, hlam]
                                                  · linarith only [h1408, h1917, hlam]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1920 | h1920
                                                  · linarith only [h1920, h879, hlam]
                                                  · linarith only [h1411, h1920, hlam]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  rcases p1820_3 (m.d 0 3) (by simp) with h1923 | h1923
                                                  · linarith only [h1923, h879, hlam]
                                                  · linarith only [h1412, h1923, hlam]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1408, hlam, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1796, hlam, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1809_1, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1809_1, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1411, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1799, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1803, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1807, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1412, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1800, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1804, hlam, p1820_0]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [h1407, h1800, h879, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1820_1]
                                                · have p1820_0 := h1820c.1
                                                  have p1820_1 := h1820c.2.1
                                                  have p1820_2 := h1820c.2.2.1
                                                  have p1820_3 := h1820c.2.2.2
                                                  linarith only [hlam, p1820_0]
                                        · linarith only [h1796, h1813, hlam]
                                      · linarith only [h1812, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1943 | h1943
                                      · rcases p1809_3 (m.d 1 2) (by simp) with h1944 | h1944
                                        · rcases p1809_3 (m.d 2 3) (by simp) with h1945 | h1945
                                          · linarith only [h1408, h1945, hlam]
                                          · linarith only [h1803, h1945, hlam]
                                        · linarith only [h1797, h1944, hlam]
                                      · linarith only [h1943, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1950 | h1950
                                      · rcases p1809_3 (m.d 1 2) (by simp) with h1951 | h1951
                                        · rcases p1809_3 (m.d 2 3) (by simp) with h1952 | h1952
                                          · linarith only [h1408, h1952, hlam]
                                          · linarith only [h1804, h1952, hlam]
                                        · linarith only [h1798, h1951, hlam]
                                      · linarith only [h1950, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1408, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1809_1, u2ehi2]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1959 | h1959
                                      · linarith only [h0, h1959, hlam]
                                      · linarith only [h1408, h1959, hlam]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1962 | h1962
                                      · linarith only [h0, h1962, hlam]
                                      · linarith only [h1409, h1962, hlam]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      rcases p1809_3 (m.d 0 2) (by simp) with h1965 | h1965
                                      · linarith only [h0, h1965, hlam]
                                      · linarith only [h1410, h1965, hlam]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1408, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1796, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hc23, hlam, hphi, p1809_1, u2ehi3]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h0, h1408, h1805, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1809_1, u2ehi3]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1409, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1797, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1803, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1805, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1410, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1798, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1804, hlam, p1809_0]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [h1407, h1798, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1809_1, u2ehi3]
                                    · have p1809_0 := h1809c.1
                                      have p1809_1 := h1809c.2.1
                                      have p1809_2 := h1809c.2.2.1
                                      have p1809_3 := h1809c.2.2.2
                                      linarith only [hlam, p1809_0]
                              · linarith only [h1407, h1796, h1800, h1804, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1411, h1413, h1803, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h1407, h1798, h1800, h879, hc35, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h1407, h1411, h1413, h1798, h1799, h879, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h0, h1408, h1798, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h1407, h1409, h1413, h1796, h1797, h879, hlam]
                · linarith only [h0, h1408, h1796, hlam]
            · linarith only [h1407, h1412, h879, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1991 | h1991
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1992 | h1992
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1993 | h1993
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1994 | h1994
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1995 | h1995
                    · linarith only [h1407, h1411, h1995, h879, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h0, h1408, h1995, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h1407, h1410, h1993, h1994, h879, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1407, h1408, h1410, h1993, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
              · linarith only [h1407, h1411, h1992, h879, hlam]
            · linarith only [h1407, h1991, h879, hlam]
        · linarith only [h1408, h1410, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1408, h1409, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2004 | h2004
      · linarith only [h1408, h2004, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2006 | h2006
        · linarith only [h1408, h2006, hc23, hlam, hphi, u2ehi4]
        · linarith only [h0, h1407, h2006, hlam]
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2 m hb2 hb3 hb5 h0 h879 h1407

end R2N4
