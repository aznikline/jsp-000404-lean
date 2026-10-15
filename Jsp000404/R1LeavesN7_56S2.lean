import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4108000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1325 | h1325
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1326 | h1326
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1327 | h1327
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1328 | h1328
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1329 | h1329
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1330 | h1330
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1332 | h1332
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1333 | h1333
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1334 | h1334
                    · linarith only [h0, h1325, h1334, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1336 | h1336
                      · linarith only [h0, h1325, h1336, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                          · linarith only [h1327, h1334, h1339, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1341 | h1341
                            · linarith only [h1331, h1336, h1341, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1343 | h1343
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1344 | h1344
                                · rcases h2bigk with h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h0, hlam, p1345_1]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1348 | h1348
                                    · rcases p1345_3 (m.d 1 2) (by simp) with h1349 | h1349
                                      · rcases p1345_3 (m.d 2 3) (by simp) with h1350 | h1350
                                        · linarith only [h1350, hlam, p1345_0]
                                        · rcases p1345_3 (m.d 2 4) (by simp) with h1352 | h1352
                                          · linarith only [h1328, h1352, hlam]
                                          · linarith only [h1339, h1352, hlam]
                                      · linarith only [h1331, h1349, hlam]
                                    · linarith only [h1348, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1357 | h1357
                                    · rcases p1345_3 (m.d 1 2) (by simp) with h1358 | h1358
                                      · rcases p1345_3 (m.d 2 3) (by simp) with h1359 | h1359
                                        · linarith only [h1327, h1359, hlam]
                                        · rcases p1345_3 (m.d 2 4) (by simp) with h1361 | h1361
                                          · linarith only [h1361, hlam, p1345_0]
                                          · rcases p1345_3 (m.d 2 5) (by simp) with h1363 | h1363
                                            · linarith only [h1329, h1363, hlam]
                                            · rcases h5bigk with h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1330, h1331, h1336, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1365_1, u3ehi2]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h0, h1326, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h0, h1326, h1331, h1336, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1365_1, u3ehi2]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h0, h1326, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1326, hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1338, h1341, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1365_1, u3ehi2]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1336, hlam, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h0, h1326, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1329, hlam, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1333, hlam, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1341, hlam, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h0, h1329, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1365_1]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1344, hc34, hlam, hphi, ht01, ht12, ht23, p1365_1, u0ehi4]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1331, h1336, h1344, hc34, hlam, hphi, p1365_1, u3ehi2]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1341, h1344, hc34, hlam, hphi, p1365_1, u3ehi2]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                rcases p1365_3 (m.d 0 5) (by simp) with h1385 | h1385
                                                · linarith only [h0, h1326, h1385, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1365_1]
                                                · linarith only [h1330, h1385, hlam]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1330, hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1338, hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1343, hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [h1344, hlam, p1365_0]
                                              · have p1365_0 := h1365c.1
                                                have p1365_1 := h1365c.2.1
                                                have p1365_2 := h1365c.2.2.1
                                                have p1365_3 := h1365c.2.2.2
                                                linarith only [hlam, p1365_0]
                                      · linarith only [h1332, h1358, hlam]
                                    · linarith only [h1357, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1395 | h1395
                                    · rcases p1345_3 (m.d 1 2) (by simp) with h1396 | h1396
                                      · rcases p1345_3 (m.d 2 3) (by simp) with h1397 | h1397
                                        · linarith only [h1327, h1397, hlam]
                                        · rcases p1345_3 (m.d 2 4) (by simp) with h1399 | h1399
                                          · linarith only [h1328, h1399, hlam]
                                          · linarith only [h1343, h1399, hlam]
                                      · linarith only [h1333, h1396, hlam]
                                    · linarith only [h1395, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1345_1, u0ehi1]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1406 | h1406
                                    · linarith only [h0, h1406, hlam]
                                    · linarith only [h1327, h1406, hlam]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1409 | h1409
                                    · linarith only [h0, h1409, hlam]
                                    · linarith only [h1328, h1409, hlam]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    rcases p1345_3 (m.d 0 2) (by simp) with h1412 | h1412
                                    · linarith only [h0, h1412, hlam]
                                    · linarith only [h1329, h1412, hlam]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1327, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1331, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1339, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1341, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1328, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1332, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1328, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1345_1, u3ehi2]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h0, h1328, h1341, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1345_1, u3ehi2]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1329, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1333, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h0, h1329, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1345_1, u3ehi2]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [h1343, hlam, p1345_0]
                                  · have p1345_0 := h1345c.1
                                    have p1345_1 := h1345c.2.1
                                    have p1345_2 := h1345c.2.2.1
                                    have p1345_3 := h1345c.2.2.2
                                    linarith only [hlam, p1345_0]
                                · linarith only [h0, h1328, h1330, h1334, h1344, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h1334, h1338, h1339, h1343, hc34, hlam, hphi, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
                          · linarith only [h1331, h1336, h1432, hc35, hlam, hphi, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1434 | h1434
                            · linarith only [h1331, h1336, h1434, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1436 | h1436
                              · linarith only [h0, h1328, h1334, h1338, h1436, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1438 | h1438
                                · linarith only [h1331, h1334, h1338, h1438, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h1331, h1334, h1438, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h1333, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1332, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1331, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
                    · linarith only [h0, h1325, h1447, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1449 | h1449
                      · linarith only [h0, h1325, h1449, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                        · linarith only [h1330, h1451, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1453 | h1453
                          · linarith only [h0, h1326, h1444, h1447, h1451, h1453, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1455 | h1455
                            · linarith only [h1327, h1449, h1455, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1457 | h1457
                              · linarith only [h1330, h1445, h1457, hc14, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1459 | h1459
                                · linarith only [h0, h1326, h1330, h1444, h1447, h1451, h1459, hc12, hc34, hlam, hphi, ht01, u0ehi3, u3ehi2]
                                · linarith only [h1444, h1447, h1459, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h1446, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1325, h1444, h1445, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1325, h1444, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1326, h1329, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1466 | h1466
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1467 | h1467
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1469 | h1469
                · linarith only [h0, h1328, h1469, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h1325, h1468, h1469, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1325, h1468, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1327, h1328, h1467, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h1326, h1466, hlam]
      · linarith only [h0, h1325, h1327, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1476 | h1476
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1477 | h1477
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1478 | h1478
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1479 | h1479
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1480 | h1480
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1481 | h1481
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1482 | h1482
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1483 | h1483
                    · linarith only [h1325, h1326, h1483, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1485 | h1485
                      · linarith only [h1325, h1326, h1482, h1485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1325, h1326, h1485, hc35, hlam, hphi, u3ehi1]
                  · linarith only [h0, h1325, h1478, h1480, h1482, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1477, h1481, hlam]
              · linarith only [h0, h1325, h1480, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1491 | h1491
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1492 | h1492
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1493 | h1493
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1494 | h1494
                    · linarith only [h1325, h1326, h1493, h1494, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1496 | h1496
                      · linarith only [h1325, h1326, h1493, h1496, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1325, h1326, h1496, hc35, hlam, hphi, u3ehi1]
                  · linarith only [h0, h1478, h1493, hlam]
                · linarith only [h0, h1477, h1479, h1492, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
              · linarith only [h0, h1325, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1502 | h1502
            · linarith only [h1477, h1478, h1502, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1504 | h1504
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1505 | h1505
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1506 | h1506
                  · linarith only [h1478, h1506, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1325, h1504, h1506, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1325, h1477, h1504, h1505, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1325, h1504, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1511 | h1511
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1513 | h1513
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1514 | h1514
                · linarith only [h1477, h1514, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h1325, h1513, h1514, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1325, h1513, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1476, h1477, h1512, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1519 | h1519
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1520 | h1520
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1521 | h1521
                · linarith only [h0, h1325, h1477, h1520, h1521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1325, h1520, h1521, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1325, h1520, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h1325, h1477, h1519, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1325, h1476, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1527 | h1527
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1528 | h1528
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1529 | h1529
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1530 | h1530
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1531 | h1531
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1533 | h1533
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1534 | h1534
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1535 | h1535
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1536 | h1536
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1537 | h1537
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1538 | h1538
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1539 | h1539
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1540 | h1540
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1541 | h1541
                                · rcases h2bigk with h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h0, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1538, h1541, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1, u3ehi4]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 2) (by simp) with h1546 | h1546
                                    · rcases p1542_3 (m.d 1 2) (by simp) with h1547 | h1547
                                      · rcases p1542_3 (m.d 2 3) (by simp) with h1548 | h1548
                                        · linarith only [h1528, h1548, hlam]
                                        · linarith only [h1538, h1548, hlam]
                                      · linarith only [h1533, h1547, hlam]
                                    · linarith only [h1546, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 2) (by simp) with h1553 | h1553
                                    · rcases p1542_3 (m.d 1 2) (by simp) with h1554 | h1554
                                      · rcases p1542_3 (m.d 2 3) (by simp) with h1555 | h1555
                                        · linarith only [h1528, h1555, hlam]
                                        · linarith only [h1539, h1555, hlam]
                                      · linarith only [h1534, h1554, hlam]
                                    · linarith only [h1553, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1542_1, u0ehi1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1538, h1541, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1, u3ehi4]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 2) (by simp) with h1563 | h1563
                                    · linarith only [h0, h1563, hlam]
                                    · linarith only [h1529, h1563, hlam]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 2) (by simp) with h1566 | h1566
                                    · linarith only [h0, h1566, hlam]
                                    · linarith only [h1530, h1566, hlam]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1528, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1532, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1528, h1538, h1541, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1, u3ehi4]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h0, h1528, h1539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1, u3ehi4]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1529, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1533, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1538, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h0, h1529, h1539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1, u3ehi4]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1530, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1534, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1539, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1540, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                · linarith only [h1325, h1527, h1537, h1541, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1325, h1527, h1532, h1537, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1325, h1527, h1532, h1536, h1539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1587 | h1587
                            · linarith only [h1538, h1587, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1325, h1527, h1532, h1536, h1587, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
                              · linarith only [h1533, h1537, h1592, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1594 | h1594
                                · linarith only [h1533, h1537, h1590, h1594, hlam]
                                · rcases h2bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h0, hlam, p1596_1]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h0, h1591, h1594, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi3]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    rcases p1596_3 (m.d 0 2) (by simp) with h1600 | h1600
                                    · rcases p1596_3 (m.d 1 2) (by simp) with h1601 | h1601
                                      · rcases p1596_3 (m.d 2 3) (by simp) with h1602 | h1602
                                        · linarith only [h1528, h1602, hlam]
                                        · linarith only [h1590, h1602, hlam]
                                      · linarith only [h1533, h1601, hlam]
                                    · linarith only [h1600, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    rcases p1596_3 (m.d 0 2) (by simp) with h1607 | h1607
                                    · rcases p1596_3 (m.d 1 2) (by simp) with h1608 | h1608
                                      · rcases p1596_3 (m.d 2 3) (by simp) with h1609 | h1609
                                        · linarith only [h1528, h1609, hlam]
                                        · linarith only [h1591, h1609, hlam]
                                      · linarith only [h1534, h1608, hlam]
                                    · linarith only [h1607, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1596_1, u0ehi1]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1591, h1594, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi3]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    rcases p1596_3 (m.d 0 2) (by simp) with h1617 | h1617
                                    · linarith only [h0, h1617, hlam]
                                    · linarith only [h1529, h1617, hlam]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    rcases p1596_3 (m.d 0 2) (by simp) with h1620 | h1620
                                    · linarith only [h0, h1620, hlam]
                                    · linarith only [h1530, h1620, hlam]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1528, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1532, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1528, h1590, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi3]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h0, h1528, h1590, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi3]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1529, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1533, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1590, hlam, p1596_1]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1592, hlam, p1596_1]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1530, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1534, hlam, p1596_0]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h1591, hlam, p1596_1]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [h0, h1530, h1590, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi3]
                                  · have p1596_0 := h1596c.1
                                    have p1596_1 := h1596c.2.1
                                    have p1596_2 := h1596c.2.2.1
                                    have p1596_3 := h1596c.2.2.2
                                    linarith only [hlam, p1596_0]
                            · linarith only [h1325, h1527, h1532, h1536, h1591, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h1325, h1527, h1531, h1532, h1535, h1537, h1590, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1325, h1536, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1325, h1527, h1535, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · linarith only [h1325, h1527, h1532, h1534, hc25, hlam, hphi, ht01, ht12, u0ehi4]
                · linarith only [h1325, h1527, h1532, h1533, hc24, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h0, h1527, h1532, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1645 | h1645
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1646 | h1646
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1647 | h1647
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1648 | h1648
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1649 | h1649
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1650 | h1650
                        · linarith only [h1531, h1650, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1652 | h1652
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1653 | h1653
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1654 | h1654
                              · linarith only [h1527, h1531, h1646, h1650, h1654, hc01, hlam, hphi, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1656 | h1656
                                · linarith only [h1325, h1527, h1531, h1645, h1646, h1650, h1652, h1656, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases h2bigk with h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h0, hlam, p1658_1]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h0, h1652, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi3]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    rcases p1658_3 (m.d 0 2) (by simp) with h1662 | h1662
                                    · rcases p1658_3 (m.d 1 2) (by simp) with h1663 | h1663
                                      · rcases p1658_3 (m.d 2 3) (by simp) with h1664 | h1664
                                        · linarith only [h1528, h1664, hlam]
                                        · linarith only [h1652, h1664, hlam]
                                      · linarith only [h1646, h1663, hlam]
                                    · linarith only [h1662, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    rcases p1658_3 (m.d 0 2) (by simp) with h1669 | h1669
                                    · rcases p1658_3 (m.d 1 2) (by simp) with h1670 | h1670
                                      · rcases p1658_3 (m.d 2 3) (by simp) with h1671 | h1671
                                        · linarith only [h1528, h1671, hlam]
                                        · linarith only [h1653, h1671, hlam]
                                      · linarith only [h1647, h1670, hlam]
                                    · linarith only [h1669, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1658_1, u0ehi1]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1653, h1656, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi3]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    rcases p1658_3 (m.d 0 2) (by simp) with h1679 | h1679
                                    · linarith only [h0, h1679, hlam]
                                    · linarith only [h1529, h1679, hlam]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    rcases p1658_3 (m.d 0 2) (by simp) with h1682 | h1682
                                    · linarith only [h0, h1682, hlam]
                                    · linarith only [h1530, h1682, hlam]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1528, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1645, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1528, h1652, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi3]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h0, h1528, h1653, h1656, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi3]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1529, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1646, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1652, hlam, p1658_1]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1654, hlam, p1658_1]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1530, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1647, hlam, p1658_0]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h1653, hlam, p1658_1]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [h0, h1530, h1652, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi3]
                                  · have p1658_0 := h1658c.1
                                    have p1658_1 := h1658c.2.1
                                    have p1658_2 := h1658c.2.2.1
                                    have p1658_3 := h1658c.2.2.2
                                    linarith only [hlam, p1658_0]
                            · linarith only [h1325, h1527, h1645, h1649, h1653, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h1325, h1527, h1645, h1648, h1650, h1652, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1325, h1649, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1325, h1527, h1531, h1648, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                  · linarith only [h1325, h1527, h1531, h1645, h1647, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h1325, h1527, h1531, h1645, h1646, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h0, h1527, h1528, h1531, h1645, hc02, hlam, hphi, u0ehi3]
          · linarith only [h0, h1527, h1530, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1708 | h1708
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1709 | h1709
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1710 | h1710
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
                · linarith only [h1528, h1529, h1711, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1711, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1527, h1528, h1710, hc02, hlam, hphi, u0ehi4]
            · linarith only [h1528, h1529, h1709, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h1527, h1708, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1717 | h1717
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1718 | h1718
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1719 | h1719
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1720 | h1720
              · linarith only [h0, h1528, h1720, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h1527, h1720, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
              · linarith only [h0, h1527, h1528, h1719, h1723, hc12, hlam, hphi, ht01, u0ehi3]
              · linarith only [h0, h1527, h1719, h1723, hc23, hlam, hphi, ht01, ht12, u0ehi3]
          · linarith only [h0, h1527, h1718, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1727 | h1727
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1728 | h1728
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1729 | h1729
              · linarith only [h0, h1527, h1528, h1729, hc12, hlam, hphi, ht01, u0ehi4]
              · linarith only [h0, h1527, h1729, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h1527, h1717, h1728, hlam]
          · linarith only [h0, h1527, h1727, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1734 | h1734
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1735 | h1735
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1736 | h1736
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1737 | h1737
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1739 | h1739
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1740 | h1740
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1741 | h1741
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1742 | h1742
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1743 | h1743
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1744 | h1744
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1745 | h1745
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1746 | h1746
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1747 | h1747
                                · rcases h2bigk with h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h0, hlam, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1744, h1747, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1748_1, u3ehi4]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    rcases p1748_3 (m.d 0 2) (by simp) with h1752 | h1752
                                    · rcases p1748_3 (m.d 1 2) (by simp) with h1753 | h1753
                                      · rcases p1748_3 (m.d 2 3) (by simp) with h1754 | h1754
                                        · linarith only [h1734, h1754, hlam]
                                        · linarith only [h1744, h1754, hlam]
                                      · linarith only [h1739, h1753, hlam]
                                    · linarith only [h1752, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    rcases p1748_3 (m.d 0 2) (by simp) with h1759 | h1759
                                    · rcases p1748_3 (m.d 1 2) (by simp) with h1760 | h1760
                                      · rcases p1748_3 (m.d 2 3) (by simp) with h1761 | h1761
                                        · linarith only [h1734, h1761, hlam]
                                        · linarith only [h1745, h1761, hlam]
                                      · linarith only [h1740, h1760, hlam]
                                    · linarith only [h1759, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1748_1, u0ehi1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1744, h1747, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1748_1, u3ehi4]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    rcases p1748_3 (m.d 0 2) (by simp) with h1769 | h1769
                                    · linarith only [h0, h1769, hlam]
                                    · linarith only [h1735, h1769, hlam]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    rcases p1748_3 (m.d 0 2) (by simp) with h1772 | h1772
                                    · linarith only [h0, h1772, hlam]
                                    · linarith only [h1736, h1772, hlam]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1734, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1738, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1734, h1744, h1747, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1748_1, u3ehi4]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h0, h1734, h1745, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1748_1, u3ehi4]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1735, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1739, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1744, hlam, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h0, h1735, h1745, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1748_1, u3ehi4]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1736, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1740, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1745, hlam, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1746, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                · linarith only [h0, h1734, h1744, h1746, h1747, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1791 | h1791
                                · linarith only [h1744, h1746, h1791, hlam]
                                · rcases h2bigk with h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h0, hlam, p1793_1]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h0, h1744, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1793_1, u3ehi3]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    rcases p1793_3 (m.d 0 2) (by simp) with h1797 | h1797
                                    · rcases p1793_3 (m.d 1 2) (by simp) with h1798 | h1798
                                      · rcases p1793_3 (m.d 2 3) (by simp) with h1799 | h1799
                                        · linarith only [h1734, h1799, hlam]
                                        · linarith only [h1744, h1799, hlam]
                                      · linarith only [h1739, h1798, hlam]
                                    · linarith only [h1797, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    rcases p1793_3 (m.d 0 2) (by simp) with h1804 | h1804
                                    · rcases p1793_3 (m.d 1 2) (by simp) with h1805 | h1805
                                      · rcases p1793_3 (m.d 2 3) (by simp) with h1806 | h1806
                                        · linarith only [h1734, h1806, hlam]
                                        · linarith only [h1745, h1806, hlam]
                                      · linarith only [h1740, h1805, hlam]
                                    · linarith only [h1804, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1793_1, u0ehi1]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1745, h1791, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1793_1, u3ehi3]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    rcases p1793_3 (m.d 0 2) (by simp) with h1814 | h1814
                                    · linarith only [h0, h1814, hlam]
                                    · linarith only [h1735, h1814, hlam]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    rcases p1793_3 (m.d 0 2) (by simp) with h1817 | h1817
                                    · linarith only [h0, h1817, hlam]
                                    · linarith only [h1736, h1817, hlam]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1734, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1738, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1734, h1744, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1793_1, u3ehi3]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h0, h1734, h1744, h1746, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1793_1, u3ehi3]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1735, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1739, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1744, hlam, p1793_1]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1746, hlam, p1793_1]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1736, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1740, hlam, p1793_0]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h1745, hlam, p1793_1]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [h0, h1736, h1744, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1793_1, u3ehi3]
                                  · have p1793_0 := h1793c.1
                                    have p1793_1 := h1793c.2.1
                                    have p1793_2 := h1793c.2.2.1
                                    have p1793_3 := h1793c.2.2.2
                                    linarith only [hlam, p1793_0]
                            · linarith only [h1738, h1742, h1744, h1745, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1836 | h1836
                            · linarith only [h1744, h1836, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1838 | h1838
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1839 | h1839
                                · rcases h2bigk with h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h0, hlam, p1840_1]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1843 | h1843
                                    · rcases p1840_3 (m.d 1 2) (by simp) with h1844 | h1844
                                      · rcases p1840_3 (m.d 2 3) (by simp) with h1845 | h1845
                                        · linarith only [h1845, hlam, p1840_0]
                                        · rcases p1840_3 (m.d 2 4) (by simp) with h1847 | h1847
                                          · linarith only [h1735, h1847, hlam]
                                          · linarith only [h1744, h1847, hlam]
                                      · linarith only [h1738, h1844, hlam]
                                    · linarith only [h1843, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1852 | h1852
                                    · rcases p1840_3 (m.d 1 2) (by simp) with h1853 | h1853
                                      · rcases p1840_3 (m.d 2 3) (by simp) with h1854 | h1854
                                        · linarith only [h1734, h1854, hlam]
                                        · rcases p1840_3 (m.d 2 4) (by simp) with h1856 | h1856
                                          · linarith only [h1856, hlam, p1840_0]
                                          · rcases p1840_3 (m.d 2 5) (by simp) with h1858 | h1858
                                            · linarith only [h1736, h1858, hlam]
                                            · rcases h5bigk with h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c | h1860c
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1527, hlam, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1737, h1836, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1860_1, u3ehi2]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1527, h1738, h1741, h1743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1860_1, u3ehi4]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                rcases p1860_3 (m.d 0 5) (by simp) with h1865 | h1865
                                                · rcases p1860_3 (m.d 1 5) (by simp) with h1866 | h1866
                                                  · rcases p1860_3 (m.d 2 5) (by simp) with h1867 | h1867
                                                    · linarith only [h1736, h1867, hlam]
                                                    · linarith only [h1838, h1867, hlam]
                                                  · linarith only [h1743, h1866, hlam]
                                                · linarith only [h1737, h1865, hlam]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1738, h1741, h1743, hc12, hlam, hphi, ht01, p1860_1, u0ehi4]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1738, h1741, h1743, h1836, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1860_1, u3ehi2]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1738, h1741, h1743, h1836, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1860_1, u3ehi2]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                rcases p1860_3 (m.d 0 5) (by simp) with h1876 | h1876
                                                · linarith only [h1527, h1876, hlam]
                                                · linarith only [h1737, h1876, hlam]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1736, hlam, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1740, hlam, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1836, hlam, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h0, h1736, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1527, h1738, h1741, h1839, hc12, hlam, hphi, ht01, p1860_1, u0ehi0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1742, hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1738, h1741, h1839, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1738, h1741, h1839, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1860_1]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1737, hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1743, hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1838, hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [h1839, hlam, p1860_0]
                                              · have p1860_0 := h1860c.1
                                                have p1860_1 := h1860c.2.1
                                                have p1860_2 := h1860c.2.2.1
                                                have p1860_3 := h1860c.2.2.2
                                                linarith only [hlam, p1860_0]
                                      · linarith only [h1739, h1853, hlam]
                                    · linarith only [h1852, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1896 | h1896
                                    · rcases p1840_3 (m.d 1 2) (by simp) with h1897 | h1897
                                      · rcases p1840_3 (m.d 2 3) (by simp) with h1898 | h1898
                                        · linarith only [h1734, h1898, hlam]
                                        · rcases p1840_3 (m.d 2 4) (by simp) with h1900 | h1900
                                          · linarith only [h1735, h1900, hlam]
                                          · linarith only [h1838, h1900, hlam]
                                      · linarith only [h1740, h1897, hlam]
                                    · linarith only [h1896, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1840_1, u0ehi1]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1907 | h1907
                                    · linarith only [h0, h1907, hlam]
                                    · linarith only [h1734, h1907, hlam]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1910 | h1910
                                    · linarith only [h0, h1910, hlam]
                                    · linarith only [h1735, h1910, hlam]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    rcases p1840_3 (m.d 0 2) (by simp) with h1913 | h1913
                                    · linarith only [h0, h1913, hlam]
                                    · linarith only [h1736, h1913, hlam]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1734, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1738, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1744, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1836, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1735, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1739, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1735, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1840_1, u3ehi2]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1738, h1741, h1744, h1836, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1840_1, u3ehi2]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1736, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1740, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h0, h1736, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1840_1, u3ehi2]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [h1838, hlam, p1840_0]
                                  · have p1840_0 := h1840c.1
                                    have p1840_1 := h1840c.2.1
                                    have p1840_2 := h1840c.2.2.1
                                    have p1840_3 := h1840c.2.2.2
                                    linarith only [hlam, p1840_0]
                                · linarith only [h0, h1735, h1737, h1744, h1839, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1932 | h1932
                                · linarith only [h1738, h1741, h1744, h1838, h1932, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h1735, h1737, h1744, h1932, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h1527, h1735, h1737, h1743, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h1325, h1742, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1325, h1741, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1740, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h1325, h1738, h1739, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1738, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1941 | h1941
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1942 | h1942
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1943 | h1943
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1944 | h1944
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1945 | h1945
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1946 | h1946
                        · linarith only [h1737, h1946, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1948 | h1948
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1949 | h1949
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1950 | h1950
                              · linarith only [h1735, h1737, h1950, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1952 | h1952
                                · linarith only [h1734, h1737, h1948, h1952, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h2bigk with h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h0, hlam, p1954_1]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h0, h1949, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1954_1, u3ehi4]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    rcases p1954_3 (m.d 0 2) (by simp) with h1958 | h1958
                                    · rcases p1954_3 (m.d 1 2) (by simp) with h1959 | h1959
                                      · rcases p1954_3 (m.d 2 3) (by simp) with h1960 | h1960
                                        · linarith only [h1734, h1960, hlam]
                                        · linarith only [h1948, h1960, hlam]
                                      · linarith only [h1942, h1959, hlam]
                                    · linarith only [h1958, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    rcases p1954_3 (m.d 0 2) (by simp) with h1965 | h1965
                                    · rcases p1954_3 (m.d 1 2) (by simp) with h1966 | h1966
                                      · rcases p1954_3 (m.d 2 3) (by simp) with h1967 | h1967
                                        · linarith only [h1734, h1967, hlam]
                                        · linarith only [h1949, h1967, hlam]
                                      · linarith only [h1943, h1966, hlam]
                                    · linarith only [h1965, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p1954_1, u0ehi1]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1949, h1952, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1954_1, u3ehi3]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    rcases p1954_3 (m.d 0 2) (by simp) with h1975 | h1975
                                    · linarith only [h0, h1975, hlam]
                                    · linarith only [h1735, h1975, hlam]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    rcases p1954_3 (m.d 0 2) (by simp) with h1978 | h1978
                                    · linarith only [h0, h1978, hlam]
                                    · linarith only [h1736, h1978, hlam]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1734, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1941, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1734, h1948, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1954_1, u3ehi3]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h0, h1734, h1949, h1952, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1954_1, u3ehi3]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1735, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1942, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1948, hlam, p1954_1]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1950, hlam, p1954_1]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1736, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1943, hlam, p1954_0]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h1949, hlam, p1954_1]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [h0, h1736, h1948, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1954_1, u3ehi3]
                                  · have p1954_0 := h1954c.1
                                    have p1954_1 := h1954c.2.1
                                    have p1954_2 := h1954c.2.2.1
                                    have p1954_3 := h1954c.2.2.2
                                    linarith only [hlam, p1954_0]
                            · linarith only [h1941, h1945, h1948, h1949, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1944, h1946, h1948, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1325, h1945, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1325, h1944, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1943, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h1325, h1941, h1942, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1941, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2003 | h2003
            · linarith only [h1735, h1736, h2003, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2005 | h2005
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2006 | h2006
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2007 | h2007
                  · linarith only [h1734, h1736, h2007, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2007, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h1325, h1735, h2005, h2006, hc02, hlam, hphi, u0ehi0]
              · linarith only [h0, h2005, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2012 | h2012
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2013 | h2013
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2014 | h2014
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2015 | h2015
                · linarith only [h1734, h1735, h2015, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2015, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1734, h2014, hc02, hlam, hphi, u0ehi0]
            · linarith only [h1734, h1735, h2013, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2020 | h2020
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2021 | h2021
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2022 | h2022
                · linarith only [h1734, h1735, h2022, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2022, hc24, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1734, h2021, hc02, hlam, hphi, u0ehi0]
            · linarith only [h1734, h1735, h2020, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2027 | h2027
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2028 | h2028
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2029 | h2029
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2030 | h2030
              · linarith only [h1527, h1734, h2027, h2029, h2030, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h2030, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2033 | h2033
              · linarith only [h1734, h2033, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h2033, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2036 | h2036
            · linarith only [h2027, h2028, h2036, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2038 | h2038
              · linarith only [h1734, h2038, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h2038, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2041 | h2041
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2042 | h2042
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
              · linarith only [h1527, h1734, h2041, h2043, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h2043, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h2027, h2041, h2042, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2047 | h2047
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2048 | h2048
              · linarith only [h1734, h2048, hc12, hlam, hphi, ht01, u0ehi1]
              · linarith only [h0, h2048, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2051 | h2051
              · linarith only [h0, h1734, h2051, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h2051, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 4108000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
