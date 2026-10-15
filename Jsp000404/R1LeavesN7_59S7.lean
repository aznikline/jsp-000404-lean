import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1349 | h1349
  · linarith only [h0, h1349, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1351 | h1351
    · linarith only [h0, h1351, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1353 | h1353
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1354 | h1354
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1355 | h1355
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1356 | h1356
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1357 | h1357
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1358 | h1358
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1359 | h1359
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1360 | h1360
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1361 | h1361
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1362 | h1362
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1363 | h1363
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1364 | h1364
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1365 | h1365
                              · rcases h3bigk with h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1349, hlam, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1353, h1362, h1365, hc02, hc45, hlam, hphi, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h0, h1353, h1365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  rcases p1366_3 (m.d 0 3) (by simp) with h1371 | h1371
                                  · rcases p1366_3 (m.d 1 3) (by simp) with h1372 | h1372
                                    · rcases p1366_3 (m.d 2 3) (by simp) with h1373 | h1373
                                      · linarith only [h1353, h1373, hlam]
                                      · linarith only [h1363, h1373, hlam]
                                    · linarith only [h1360, h1372, hlam]
                                  · linarith only [h1371, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1357, h1362, h1365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1357, h1365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  rcases p1366_3 (m.d 0 3) (by simp) with h1382 | h1382
                                  · linarith only [h1349, h1382, hlam]
                                  · linarith only [h1355, h1382, hlam]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1353, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1357, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1353, h1365, hc03, hc45, hlam, hphi, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h0, h1353, h1365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1354, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1359, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1362, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1349, h1354, h1357, h1365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1366_1]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1355, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1360, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1363, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [h1365, hlam, p1366_0]
                                · have p1366_0 := h1366c.1
                                  have p1366_1 := h1366c.2.1
                                  have p1366_2 := h1366c.2.2.1
                                  have p1366_3 := h1366c.2.2.2
                                  linarith only [hlam, p1366_0]
                              · rcases h3bigk with h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1349, hlam, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1349, h1357, h1362, h1364, h1365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 3) (by simp) with h1404 | h1404
                                  · rcases p1400_3 (m.d 1 3) (by simp) with h1405 | h1405
                                    · rcases p1400_3 (m.d 2 3) (by simp) with h1406 | h1406
                                      · linarith only [h1353, h1406, hlam]
                                      · linarith only [h1362, h1406, hlam]
                                    · linarith only [h1359, h1405, hlam]
                                  · linarith only [h1404, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 3) (by simp) with h1411 | h1411
                                  · rcases p1400_3 (m.d 1 3) (by simp) with h1412 | h1412
                                    · rcases p1400_3 (m.d 2 3) (by simp) with h1413 | h1413
                                      · linarith only [h1353, h1413, hlam]
                                      · linarith only [h1363, h1413, hlam]
                                    · linarith only [h1360, h1412, hlam]
                                  · linarith only [h1411, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1400_1, u1ehi0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1357, h1362, h1364, h1365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 3) (by simp) with h1421 | h1421
                                  · linarith only [h1349, h1421, hlam]
                                  · linarith only [h1354, h1421, hlam]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 3) (by simp) with h1424 | h1424
                                  · linarith only [h1349, h1424, hlam]
                                  · linarith only [h1355, h1424, hlam]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1353, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1357, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, h1353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, h1353, h1365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1354, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1359, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1362, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1365, hlam, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1355, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1360, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1363, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1355, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1442 | h1442
                              · linarith only [h0, h1353, h1362, h1364, h1442, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h3bigk with h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1349, hlam, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1349, h1357, h1363, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  rcases p1444_3 (m.d 0 3) (by simp) with h1448 | h1448
                                  · rcases p1444_3 (m.d 1 3) (by simp) with h1449 | h1449
                                    · rcases p1444_3 (m.d 2 3) (by simp) with h1450 | h1450
                                      · linarith only [h1353, h1450, hlam]
                                      · linarith only [h1362, h1450, hlam]
                                    · linarith only [h1359, h1449, hlam]
                                  · linarith only [h1448, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  rcases p1444_3 (m.d 0 3) (by simp) with h1455 | h1455
                                  · rcases p1444_3 (m.d 1 3) (by simp) with h1456 | h1456
                                    · rcases p1444_3 (m.d 2 3) (by simp) with h1457 | h1457
                                      · linarith only [h1353, h1457, hlam]
                                      · linarith only [h1363, h1457, hlam]
                                    · linarith only [h1360, h1456, hlam]
                                  · linarith only [h1455, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1444_1, u1ehi0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1357, h1363, h1442, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  rcases p1444_3 (m.d 0 3) (by simp) with h1465 | h1465
                                  · linarith only [h1349, h1465, hlam]
                                  · linarith only [h1354, h1465, hlam]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  rcases p1444_3 (m.d 0 3) (by simp) with h1468 | h1468
                                  · linarith only [h1349, h1468, hlam]
                                  · linarith only [h1355, h1468, hlam]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1353, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1357, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h0, h1353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h0, h1353, h1442, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1354, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1359, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1362, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1442, hlam, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1355, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1360, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1363, hlam, p1444_0]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [h1349, h1355, h1357, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1444_1]
                                · have p1444_0 := h1444c.1
                                  have p1444_1 := h1444c.2.1
                                  have p1444_2 := h1444c.2.2.1
                                  have p1444_3 := h1444c.2.2.2
                                  linarith only [hlam, p1444_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1486 | h1486
                            · linarith only [h1362, h1363, h1486, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1488 | h1488
                              · linarith only [h1362, h1363, h1486, h1488, hlam]
                              · rcases h3bigk with h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1349, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1349, h1357, h1362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 3) (by simp) with h1494 | h1494
                                  · rcases p1490_3 (m.d 1 3) (by simp) with h1495 | h1495
                                    · rcases p1490_3 (m.d 2 3) (by simp) with h1496 | h1496
                                      · linarith only [h1353, h1496, hlam]
                                      · linarith only [h1362, h1496, hlam]
                                    · linarith only [h1359, h1495, hlam]
                                  · linarith only [h1494, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1349, h1357, h1362, h1363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1490_1, u1ehi0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1357, h1362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 3) (by simp) with h1505 | h1505
                                  · linarith only [h1349, h1505, hlam]
                                  · linarith only [h1354, h1505, hlam]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1357, h1362, h1363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1353, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1357, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1363, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1363, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1354, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1359, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1362, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1488, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1355, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1360, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1351, h1356, h1357, h1359, h1488, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1524 | h1524
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1525 | h1525
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1526 | h1526
                              · rcases h3bigk with h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1349, hlam, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1349, h1357, h1524, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1349, h1357, h1362, h1524, h1526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  rcases p1527_3 (m.d 0 3) (by simp) with h1532 | h1532
                                  · rcases p1527_3 (m.d 1 3) (by simp) with h1533 | h1533
                                    · rcases p1527_3 (m.d 2 3) (by simp) with h1534 | h1534
                                      · linarith only [h1353, h1534, hlam]
                                      · linarith only [h1524, h1534, hlam]
                                    · linarith only [h1360, h1533, hlam]
                                  · linarith only [h1532, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1527_1, u1ehi0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1357, h1524, h1526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1357, h1362, h1524, h1526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  rcases p1527_3 (m.d 0 3) (by simp) with h1543 | h1543
                                  · linarith only [h1349, h1543, hlam]
                                  · linarith only [h1355, h1543, hlam]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1353, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1357, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1362, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1354, h1362, h1526, hc03, hc45, hlam, hphi, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1354, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1359, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1354, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1349, h1354, h1357, h1526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1527_1]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1355, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1360, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1524, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [h1526, hlam, p1527_0]
                                · have p1527_0 := h1527c.1
                                  have p1527_1 := h1527c.2.1
                                  have p1527_2 := h1527c.2.2.1
                                  have p1527_3 := h1527c.2.2.2
                                  linarith only [hlam, p1527_0]
                              · linarith only [h1349, h1354, h1356, h1357, h1362, h1524, h1526, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1362, h1524, h1525, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1563 | h1563
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1564 | h1564
                              · rcases h3bigk with h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1349, hlam, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  rcases p1565_3 (m.d 0 3) (by simp) with h1568 | h1568
                                  · rcases p1565_3 (m.d 1 3) (by simp) with h1569 | h1569
                                    · rcases p1565_3 (m.d 2 3) (by simp) with h1570 | h1570
                                      · linarith only [h1353, h1570, hlam]
                                      · rcases p1565_3 (m.d 3 4) (by simp) with h1572 | h1572
                                        · linarith only [h1354, h1572, hlam]
                                        · linarith only [h1362, h1572, hlam]
                                    · linarith only [h1357, h1569, hlam]
                                  · linarith only [h1353, h1568, hlam]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1349, h1357, h1524, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1349, h1357, h1524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1565_1, u1ehi0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  rcases p1565_3 (m.d 0 3) (by simp) with h1581 | h1581
                                  · linarith only [h1349, h1581, hlam]
                                  · linarith only [h1353, h1581, hlam]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1357, h1524, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1357, h1524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1353, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1357, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1362, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1524, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1354, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1359, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1354, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1349, h1354, h1357, h1524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1355, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1360, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1564, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                              · linarith only [h1358, h1362, h1563, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1602 | h1602
                              · rcases h3bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1349, hlam, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  rcases p1603_3 (m.d 0 3) (by simp) with h1606 | h1606
                                  · rcases p1603_3 (m.d 1 3) (by simp) with h1607 | h1607
                                    · rcases p1603_3 (m.d 2 3) (by simp) with h1608 | h1608
                                      · linarith only [h1353, h1608, hlam]
                                      · rcases p1603_3 (m.d 3 4) (by simp) with h1610 | h1610
                                        · linarith only [h1354, h1610, hlam]
                                        · linarith only [h1362, h1610, hlam]
                                    · linarith only [h1357, h1607, hlam]
                                  · linarith only [h1353, h1606, hlam]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1349, h1357, h1362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1349, h1357, h1524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1603_1, u1ehi0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  rcases p1603_3 (m.d 0 3) (by simp) with h1619 | h1619
                                  · linarith only [h1349, h1619, hlam]
                                  · linarith only [h1353, h1619, hlam]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1357, h1362, h1563, h1602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1357, h1362, h1563, h1602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1353, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1357, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1362, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1524, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1354, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1359, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1354, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1349, h1354, h1357, h1362, h1563, h1602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1355, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1360, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p1603_1]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [h1602, hlam, p1603_0]
                                · have p1603_0 := h1603c.1
                                  have p1603_1 := h1603c.2.1
                                  have p1603_2 := h1603c.2.2.1
                                  have p1603_3 := h1603c.2.2.2
                                  linarith only [hlam, p1603_0]
                              · rcases h3bigk with h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c | h1639c
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1349, hlam, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  rcases p1639_3 (m.d 0 3) (by simp) with h1642 | h1642
                                  · rcases p1639_3 (m.d 1 3) (by simp) with h1643 | h1643
                                    · rcases p1639_3 (m.d 2 3) (by simp) with h1644 | h1644
                                      · linarith only [h1353, h1644, hlam]
                                      · rcases p1639_3 (m.d 3 4) (by simp) with h1646 | h1646
                                        · linarith only [h1354, h1646, hlam]
                                        · linarith only [h1362, h1646, hlam]
                                    · linarith only [h1357, h1643, hlam]
                                  · linarith only [h1353, h1642, hlam]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1349, h1357, h1362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1349, h1357, h1524, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1349, h1357, hc12, hlam, hphi, p1639_1, u1ehi0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  rcases p1639_3 (m.d 0 3) (by simp) with h1655 | h1655
                                  · linarith only [h1349, h1655, hlam]
                                  · linarith only [h1353, h1655, hlam]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1357, h1362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1357, h1362, h1602, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1353, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1357, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1362, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1524, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1354, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1359, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1602, hlam, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1355, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1360, hlam, p1639_0]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1355, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [h1351, h1356, h1357, h1359, h1602, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1639_1]
                                · have p1639_0 := h1639c.1
                                  have p1639_1 := h1639c.2.1
                                  have p1639_2 := h1639c.2.2.1
                                  have p1639_3 := h1639c.2.2.2
                                  linarith only [hlam, p1639_0]
                      · linarith only [h1351, h1356, h1361, hlam]
                    · linarith only [h1349, h1360, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h1349, h1359, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h1358, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1357, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1680 | h1680
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1682 | h1682
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1683 | h1683
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                      · linarith only [h1351, h1356, h1680, h1682, h1684, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1351, h1684, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                    · linarith only [h0, h1353, h1355, h1683, hc12, hlam, hphi, u1ehi2]
                  · linarith only [h1349, h1682, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h1681, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1353, h1680, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1691 | h1691
            · linarith only [h1354, h1355, h1691, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1693 | h1693
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1694 | h1694
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1695 | h1695
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1696 | h1696
                    · linarith only [h1351, h1354, h1355, h1693, h1696, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h1349, h1696, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h1349, h1354, h1695, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · linarith only [h0, h1694, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1353, h1693, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1704 | h1704
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1705 | h1705
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
                  · linarith only [h1349, h1354, h1704, h1706, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h1349, h1706, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h1705, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1353, h1704, hlam]
            · linarith only [h1354, h1702, h1703, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1712 | h1712
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1713 | h1713
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1714 | h1714
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1715 | h1715
                  · linarith only [h1349, h1354, h1713, h1715, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h1349, h1715, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h1714, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1353, h1713, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1720 | h1720
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1721 | h1721
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h1349, h1354, h1720, h1722, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h1349, h1722, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h1721, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h1353, h1720, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1727 | h1727
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1728 | h1728
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1729 | h1729
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1730 | h1730
              · linarith only [h0, h1353, h1730, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1730, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1733 | h1733
              · linarith only [h0, h1353, h1733, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1733, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1736 | h1736
            · linarith only [h1727, h1728, h1736, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
              · linarith only [h0, h1353, h1738, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1738, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1741 | h1741
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1742 | h1742
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1743 | h1743
              · linarith only [h0, h1353, h1743, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1743, hc23, hlam, hphi, ht12, u1ehi0]
            · linarith only [h1727, h1741, h1742, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1747 | h1747
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1748 | h1748
              · linarith only [h0, h1353, h1748, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1748, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1751 | h1751
              · linarith only [h0, h1353, h1751, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h1751, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_23_L_R_H_I_x0 m hb1 hb3 h0
  · exact r1l7_11_23_L_R_H_I_x1 m hb1 hb3 h0

end R2N4
