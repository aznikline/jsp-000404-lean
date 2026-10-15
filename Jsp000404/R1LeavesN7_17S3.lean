import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6988000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s6_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1289 | h1289
          · linarith only [h1289, h2, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1291 | h1291
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1292 | h1292
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1293 | h1293
                · linarith only [h1286, h1293, h2, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1295 | h1295
                  · linarith only [h1291, h1295, h5, h9, hlam]
                  · rcases h0bigk with h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h0, h1285, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h1292, h1295, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1301 | h1301
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1302 | h1302
                        · linarith only [h0, h1302, hlam]
                        · linarith only [h1302, h5, hlam]
                      · linarith only [h1301, h2, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1306 | h1306
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1307 | h1307
                        · linarith only [h0, h1307, hlam]
                        · linarith only [h1307, h6, hlam]
                      · linarith only [h1306, h3, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h0, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h1, h1285, h1292, h1295, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1314 | h1314
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1315 | h1315
                        · rcases p1297_3 (m.d 0 3) (by simp) with h1316 | h1316
                          · linarith only [h1316, h4, hlam]
                          · linarith only [h1316, h7, hlam]
                        · linarith only [h1315, h5, hlam]
                      · linarith only [h1314, h2, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1321 | h1321
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1322 | h1322
                        · rcases p1297_3 (m.d 0 3) (by simp) with h1323 | h1323
                          · linarith only [h1323, h4, hlam]
                          · linarith only [h1323, h8, hlam]
                        · linarith only [h1322, h6, hlam]
                      · linarith only [h1321, h3, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h1, hlam, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h4, hlam, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1331 | h1331
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1332 | h1332
                        · rcases p1297_3 (m.d 0 3) (by simp) with h1333 | h1333
                          · rcases p1297_3 (m.d 0 4) (by simp) with h1334 | h1334
                            · linarith only [h1334, h7, hlam]
                            · rcases p1297_3 (m.d 0 5) (by simp) with h1336 | h1336
                              · linarith only [h1336, h8, hlam]
                              · linarith only [h1336, h9, hlam]
                          · linarith only [h1333, h7, hlam]
                        · linarith only [h1332, h5, hlam]
                      · linarith only [h1331, h2, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      rcases p1297_3 (m.d 0 1) (by simp) with h1342 | h1342
                      · rcases p1297_3 (m.d 0 2) (by simp) with h1343 | h1343
                        · rcases p1297_3 (m.d 0 3) (by simp) with h1344 | h1344
                          · rcases p1297_3 (m.d 0 4) (by simp) with h1345 | h1345
                            · linarith only [h1345, h7, hlam]
                            · rcases p1297_3 (m.d 0 5) (by simp) with h1347 | h1347
                              · linarith only [h1347, h8, hlam]
                              · rcases h0emin with h1349 | h1349 | h1349 | h1349 | h1349
                                · rcases h2bigk with h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h0, h1285, h1292, h1295, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    rcases p1350_3 (m.d 0 2) (by simp) with h1353 | h1353
                                    · rcases p1350_3 (m.d 1 2) (by simp) with h1354 | h1354
                                      · linarith only [h0, h1354, hlam]
                                      · linarith only [h1285, h1354, hlam]
                                    · linarith only [h1353, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1286, h2, h4, h9, hlam, p1297_1, p1350_2]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1287, h3, h4, hlam, p1297_1, p1350_2]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h0, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h0, h1292, h1295, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    rcases p1350_3 (m.d 0 2) (by simp) with h1363 | h1363
                                    · rcases p1350_3 (m.d 1 2) (by simp) with h1364 | h1364
                                      · rcases p1350_3 (m.d 2 3) (by simp) with h1365 | h1365
                                        · linarith only [h1285, h1365, hlam]
                                        · linarith only [h1291, h1365, hlam]
                                      · linarith only [h1364, hlam, p1350_0]
                                    · linarith only [h1363, h5, hlam]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    rcases p1350_3 (m.d 0 2) (by simp) with h1370 | h1370
                                    · rcases p1350_3 (m.d 1 2) (by simp) with h1371 | h1371
                                      · rcases p1350_3 (m.d 2 3) (by simp) with h1372 | h1372
                                        · linarith only [h1285, h1372, hlam]
                                        · linarith only [h1292, h1372, hlam]
                                      · linarith only [h1371, hlam, p1350_0]
                                    · linarith only [h1370, h6, hlam]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h4, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1285, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h0, h1285, h1291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h0, h1285, hc01, hc25, hlam, hphi, ht0b, ht5b, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h5, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1286, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1291, hlam, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1293, hlam, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h6, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1287, hlam, p1350_0]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1292, hlam, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [h1291, h4, h6, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1297_1, p1350_1]
                                  · have p1350_0 := h1350c.1
                                    have p1350_1 := h1350c.2.1
                                    have p1350_2 := h1350c.2.2.1
                                    have p1350_3 := h1350c.2.2.2
                                    linarith only [hlam, p1350_0]
                                · rcases h2bigk with h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, h1285, h1291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    rcases p1392_3 (m.d 0 2) (by simp) with h1395 | h1395
                                    · rcases p1392_3 (m.d 1 2) (by simp) with h1396 | h1396
                                      · linarith only [h0, h1396, hlam]
                                      · linarith only [h1285, h1396, hlam]
                                    · linarith only [h1395, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1286, h2, h4, h9, hlam, p1297_1, p1392_2]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1287, h3, h4, hlam, p1297_1, p1392_2]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, h1292, h1295, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    rcases p1392_3 (m.d 0 2) (by simp) with h1405 | h1405
                                    · rcases p1392_3 (m.d 1 2) (by simp) with h1406 | h1406
                                      · rcases p1392_3 (m.d 2 3) (by simp) with h1407 | h1407
                                        · linarith only [h1285, h1407, hlam]
                                        · linarith only [h1291, h1407, hlam]
                                      · linarith only [h1406, hlam, p1392_0]
                                    · linarith only [h1405, h5, hlam]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    rcases p1392_3 (m.d 0 2) (by simp) with h1412 | h1412
                                    · rcases p1392_3 (m.d 1 2) (by simp) with h1413 | h1413
                                      · rcases p1392_3 (m.d 2 3) (by simp) with h1414 | h1414
                                        · linarith only [h1285, h1414, hlam]
                                        · linarith only [h1292, h1414, hlam]
                                      · linarith only [h1413, hlam, p1392_0]
                                    · linarith only [h1412, h6, hlam]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h4, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1285, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, h1285, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, h1285, hc01, hc25, hlam, hphi, ht0b, ht5b, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h5, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1286, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1291, hlam, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1293, hlam, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h6, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1287, hlam, p1392_0]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h1292, hlam, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [h0, h1291, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1297_1, p1392_1]
                                  · have p1392_0 := h1392c.1
                                    have p1392_1 := h1392c.2.1
                                    have p1392_2 := h1392c.2.2.1
                                    have p1392_3 := h1392c.2.2.2
                                    linarith only [hlam, p1392_0]
                                · rcases h2bigk with h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, h1285, h1291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    rcases p1434_3 (m.d 0 2) (by simp) with h1437 | h1437
                                    · rcases p1434_3 (m.d 1 2) (by simp) with h1438 | h1438
                                      · linarith only [h0, h1438, hlam]
                                      · linarith only [h1285, h1438, hlam]
                                    · linarith only [h1437, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h4, h5, h9, hlam, p1297_1, p1434_2]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1287, h3, h4, hlam, p1297_1, p1434_2]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, h1292, h1295, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    rcases p1434_3 (m.d 0 2) (by simp) with h1447 | h1447
                                    · rcases p1434_3 (m.d 1 2) (by simp) with h1448 | h1448
                                      · rcases p1434_3 (m.d 2 3) (by simp) with h1449 | h1449
                                        · linarith only [h1285, h1449, hlam]
                                        · linarith only [h1291, h1449, hlam]
                                      · linarith only [h1448, hlam, p1434_0]
                                    · linarith only [h1447, h5, hlam]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    rcases p1434_3 (m.d 0 2) (by simp) with h1454 | h1454
                                    · rcases p1434_3 (m.d 1 2) (by simp) with h1455 | h1455
                                      · rcases p1434_3 (m.d 2 3) (by simp) with h1456 | h1456
                                        · linarith only [h1285, h1456, hlam]
                                        · linarith only [h1292, h1456, hlam]
                                      · linarith only [h1455, hlam, p1434_0]
                                    · linarith only [h1454, h6, hlam]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h4, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1285, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, h1285, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, h1285, hc01, hc25, hlam, hphi, ht0b, ht5b, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h5, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1286, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1291, hlam, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1293, hlam, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h6, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1287, hlam, p1434_0]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h1292, hlam, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [h0, h1291, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1297_1, p1434_1]
                                  · have p1434_0 := h1434c.1
                                    have p1434_1 := h1434c.2.1
                                    have p1434_2 := h1434c.2.2.1
                                    have p1434_3 := h1434c.2.2.2
                                    linarith only [hlam, p1434_0]
                                · linarith only [h0, h1349, h4, h9, hc01, hlam, p1297_1]
                                · linarith only [h0, h1349, h4, hc01, hlam, p1297_1]
                          · linarith only [h1344, h8, hlam]
                        · linarith only [h1343, h6, hlam]
                      · linarith only [h1342, h3, hlam]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h2, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h5, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h7, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h9, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h3, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h6, hlam, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h8, hlam, p1297_0]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [h1291, h5, h9, hc34, hc45, hlam, hphi, p1297_1]
                    · have p1297_0 := h1297c.1
                      have p1297_1 := h1297c.2.1
                      have p1297_2 := h1297c.2.2.1
                      have p1297_3 := h1297c.2.2.2
                      linarith only [hlam, p1297_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1491 | h1491
                · linarith only [h1286, h1491, h2, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1493 | h1493
                  · linarith only [h1291, h1292, h1493, h8, h9, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c | h1495c
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h0, h1287, hc01, hc25, hlam, hphi, ht0b, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1, h1285, h1291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      rcases p1495_3 (m.d 0 1) (by simp) with h1499 | h1499
                      · rcases p1495_3 (m.d 0 2) (by simp) with h1500 | h1500
                        · linarith only [h0, h1500, hlam]
                        · linarith only [h1500, h5, hlam]
                      · linarith only [h1499, h2, hlam]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1291, h1292, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h0, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1291, h1292, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      rcases p1495_3 (m.d 0 1) (by simp) with h1508 | h1508
                      · rcases p1495_3 (m.d 0 2) (by simp) with h1509 | h1509
                        · rcases p1495_3 (m.d 0 3) (by simp) with h1510 | h1510
                          · linarith only [h1510, h4, hlam]
                          · linarith only [h1510, h7, hlam]
                        · linarith only [h1509, h5, hlam]
                      · linarith only [h1508, h2, hlam]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h0, h1291, h1292, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1, hlam, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h4, hlam, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      rcases p1495_3 (m.d 0 1) (by simp) with h1519 | h1519
                      · rcases p1495_3 (m.d 0 2) (by simp) with h1520 | h1520
                        · rcases p1495_3 (m.d 0 3) (by simp) with h1521 | h1521
                          · rcases p1495_3 (m.d 0 4) (by simp) with h1522 | h1522
                            · linarith only [h1522, h7, hlam]
                            · rcases p1495_3 (m.d 0 5) (by simp) with h1524 | h1524
                              · linarith only [h1524, h8, hlam]
                              · linarith only [h1524, h9, hlam]
                          · linarith only [h1521, h7, hlam]
                        · linarith only [h1520, h5, hlam]
                      · linarith only [h1519, h2, hlam]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1291, h1292, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h2, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h5, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h7, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h9, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h3, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h6, hlam, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h8, hlam, p1495_0]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [h1286, h1291, h2, h9, hc34, hc45, hlam, hphi, p1495_1]
                    · have p1495_0 := h1495c.1
                      have p1495_1 := h1495c.2.1
                      have p1495_2 := h1495c.2.2.1
                      have p1495_3 := h1495c.2.2.2
                      linarith only [hlam, p1495_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1541 | h1541
              · linarith only [h0, h1285, h1288, h1291, h1541, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1543 | h1543
                · linarith only [h0, h1288, h1291, h1543, h2, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1545 | h1545
                  · linarith only [h1288, h1545, h2, h9, hlam]
                  · rcases h0bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1291, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1288, h1291, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1288, h1289, h1291, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h0, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h0, h1291, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h0, h1291, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1, hlam, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h4, hlam, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1291, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h0, h1291, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h2, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h5, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h7, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h9, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h3, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h6, hlam, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h8, hlam, p1547_0]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [h1291, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1547_1]
                    · have p1547_0 := h1547c.1
                      have p1547_1 := h1547c.2.1
                      have p1547_2 := h1547c.2.2.1
                      have p1547_3 := h1547c.2.2.2
                      linarith only [hlam, p1547_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1573 | h1573
          · linarith only [h1288, h1573, h7, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1575 | h1575
            · linarith only [h1285, h1288, h1575, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1577 | h1577
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1578 | h1578
                · linarith only [h0, h1285, h1286, h1288, h1577, h1578, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1575, h1577, h1578, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1581 | h1581
                · linarith only [h0, h1288, h1581, h5, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1583 | h1583
                  · linarith only [h1583, h7, h9, hlam]
                  · rcases h0bigk with h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h1583, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h0, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h1583, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h0, h1285, h1288, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h0, h1285, h1288, h1583, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1, hlam, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h4, hlam, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h0, h1285, h1288, h1583, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h2, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h5, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h7, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h9, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h3, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h6, hlam, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h8, hlam, p1585_0]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [h1285, h1288, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                    · have p1585_0 := h1585c.1
                      have p1585_1 := h1585c.2.1
                      have p1585_2 := h1585c.2.2.1
                      have p1585_3 := h1585c.2.2.2
                      linarith only [hlam, p1585_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1611 | h1611
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1612 | h1612
          · linarith only [h1, h1286, h1287, h1611, h1612, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1614 | h1614
            · linarith only [h0, h1285, h1287, h1614, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1285, h1287, h1611, h1614, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1617 | h1617
          · linarith only [h1611, h1617, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1619 | h1619
            · linarith only [h1285, h1611, h1619, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1621 | h1621
              · linarith only [h0, h1285, h1287, h1621, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1623 | h1623
                · linarith only [h1286, h1287, h1621, h1623, h8, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h1286, h1287, h1619, h1621, h1625, h8, h9, hc23, hc34, hlam, hphi]
                  · rcases h0bigk with h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1286, h1287, h1619, h1621, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1286, h1287, h1619, h1621, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1285, h1611, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1286, h1287, h1619, h1621, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h0, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1286, h1287, h1619, h1621, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h0, h1285, h1611, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h0, h1286, h1287, h1619, h1621, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h1, hlam, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h4, hlam, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h0, h1285, h1611, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h0, h1286, h1287, h1619, h1621, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h2, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h5, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h7, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h9, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h3, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h6, hlam, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h8, hlam, p1627_0]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [h9, hc04, hc45, hlam, hphi, p1627_1]
                    · have p1627_0 := h1627c.1
                      have p1627_1 := h1627c.2.1
                      have p1627_2 := h1627c.2.2.1
                      have p1627_3 := h1627c.2.2.2
                      linarith only [hlam, p1627_0]
    · linarith only [h1285, h1286, h5, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1654 | h1654
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1655 | h1655
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1656 | h1656
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1657 | h1657
          · linarith only [h1657, h2, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1659 | h1659
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1660 | h1660
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1661 | h1661
                · linarith only [h1285, h1654, h1661, h2, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1663 | h1663
                  · linarith only [h1654, h1659, h1663, h2, h9, hlam]
                  · rcases h0bigk with h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h1285, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h1, h1285, h1655, h1660, hc01, hc35, hlam, hphi, ht0b, ht5b, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1669 | h1669
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1670 | h1670
                        · linarith only [h0, h1670, hlam]
                        · linarith only [h1670, h5, hlam]
                      · linarith only [h1669, h2, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1674 | h1674
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1675 | h1675
                        · linarith only [h0, h1675, hlam]
                        · linarith only [h1675, h6, hlam]
                      · linarith only [h1674, h3, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h0, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h1285, h1655, h1659, h1661, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1682 | h1682
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1683 | h1683
                        · rcases p1665_3 (m.d 0 3) (by simp) with h1684 | h1684
                          · linarith only [h1684, h4, hlam]
                          · linarith only [h1684, h7, hlam]
                        · linarith only [h1683, h5, hlam]
                      · linarith only [h1682, h2, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1689 | h1689
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1690 | h1690
                        · rcases p1665_3 (m.d 0 3) (by simp) with h1691 | h1691
                          · linarith only [h1691, h4, hlam]
                          · linarith only [h1691, h8, hlam]
                        · linarith only [h1690, h6, hlam]
                      · linarith only [h1689, h3, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h1, hlam, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h4, hlam, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1699 | h1699
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1700 | h1700
                        · rcases p1665_3 (m.d 0 3) (by simp) with h1701 | h1701
                          · rcases p1665_3 (m.d 0 4) (by simp) with h1702 | h1702
                            · linarith only [h1702, h7, hlam]
                            · rcases p1665_3 (m.d 0 5) (by simp) with h1704 | h1704
                              · linarith only [h1704, h8, hlam]
                              · linarith only [h1704, h9, hlam]
                          · linarith only [h1701, h7, hlam]
                        · linarith only [h1700, h5, hlam]
                      · linarith only [h1699, h2, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      rcases p1665_3 (m.d 0 1) (by simp) with h1710 | h1710
                      · rcases p1665_3 (m.d 0 2) (by simp) with h1711 | h1711
                        · rcases p1665_3 (m.d 0 3) (by simp) with h1712 | h1712
                          · rcases p1665_3 (m.d 0 4) (by simp) with h1713 | h1713
                            · linarith only [h1713, h7, hlam]
                            · rcases p1665_3 (m.d 0 5) (by simp) with h1715 | h1715
                              · linarith only [h1715, h8, hlam]
                              · rcases h0emin with h1717 | h1717 | h1717 | h1717 | h1717
                                · rcases h2bigk with h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    rcases p1718_3 (m.d 0 2) (by simp) with h1720 | h1720
                                    · rcases p1718_3 (m.d 1 2) (by simp) with h1721 | h1721
                                      · linarith only [h0, h1721, hlam]
                                      · rcases p1718_3 (m.d 2 3) (by simp) with h1723 | h1723
                                        · linarith only [h1723, h4, hlam]
                                        · linarith only [h1285, h1723, hlam]
                                    · linarith only [h0, h1720, hlam]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h0, h1285, h1655, h1659, h1661, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1285, h1655, h1661, h4, hlam, p1718_2]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1285, h1655, h4, hlam, p1718_2]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h0, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1285, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1285, h1659, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h0, h1285, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h4, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h0, h1654, h1659, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    rcases p1718_3 (m.d 0 2) (by simp) with h1738 | h1738
                                    · rcases p1718_3 (m.d 1 2) (by simp) with h1739 | h1739
                                      · linarith only [h1285, h1739, hlam]
                                      · linarith only [h1654, h1739, hlam]
                                    · linarith only [h1738, h5, hlam]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    rcases p1718_3 (m.d 0 2) (by simp) with h1743 | h1743
                                    · rcases p1718_3 (m.d 1 2) (by simp) with h1744 | h1744
                                      · linarith only [h1285, h1744, hlam]
                                      · linarith only [h1655, h1744, hlam]
                                    · linarith only [h1743, h6, hlam]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h5, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1654, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1659, hlam, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1661, hlam, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h6, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1655, hlam, p1718_0]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h1660, hlam, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [h0, h1655, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1718_1]
                                  · have p1718_0 := h1718c.1
                                    have p1718_1 := h1718c.2.1
                                    have p1718_2 := h1718c.2.2.1
                                    have p1718_3 := h1718c.2.2.2
                                    linarith only [hlam, p1718_0]
                                · rcases h2bigk with h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    rcases p1758_3 (m.d 0 2) (by simp) with h1760 | h1760
                                    · rcases p1758_3 (m.d 1 2) (by simp) with h1761 | h1761
                                      · linarith only [h0, h1761, hlam]
                                      · rcases p1758_3 (m.d 2 3) (by simp) with h1763 | h1763
                                        · linarith only [h1763, h4, hlam]
                                        · linarith only [h1285, h1763, hlam]
                                    · linarith only [h0, h1760, hlam]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h0, h1285, h1654, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1654, h2, h4, h9, hlam, p1665_1, p1758_2]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1655, h3, h4, hlam, p1665_1, p1758_2]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h0, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1285, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1285, h1659, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h0, h1285, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h4, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h0, h1654, h1659, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    rcases p1758_3 (m.d 0 2) (by simp) with h1778 | h1778
                                    · rcases p1758_3 (m.d 1 2) (by simp) with h1779 | h1779
                                      · linarith only [h1285, h1779, hlam]
                                      · linarith only [h1654, h1779, hlam]
                                    · linarith only [h1778, h5, hlam]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    rcases p1758_3 (m.d 0 2) (by simp) with h1783 | h1783
                                    · rcases p1758_3 (m.d 1 2) (by simp) with h1784 | h1784
                                      · linarith only [h1285, h1784, hlam]
                                      · linarith only [h1655, h1784, hlam]
                                    · linarith only [h1783, h6, hlam]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h5, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1654, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1659, hlam, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1661, hlam, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h6, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1655, hlam, p1758_0]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h1660, hlam, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [h0, h1655, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1758_1]
                                  · have p1758_0 := h1758c.1
                                    have p1758_1 := h1758c.2.1
                                    have p1758_2 := h1758c.2.2.1
                                    have p1758_3 := h1758c.2.2.2
                                    linarith only [hlam, p1758_0]
                                · rcases h2bigk with h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    rcases p1798_3 (m.d 0 2) (by simp) with h1800 | h1800
                                    · rcases p1798_3 (m.d 1 2) (by simp) with h1801 | h1801
                                      · linarith only [h0, h1801, hlam]
                                      · rcases p1798_3 (m.d 2 3) (by simp) with h1803 | h1803
                                        · linarith only [h1803, h4, hlam]
                                        · linarith only [h1285, h1803, hlam]
                                    · linarith only [h0, h1800, hlam]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h0, h1285, h1654, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1654, h2, h4, h9, hlam, p1665_1, p1798_2]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1655, h3, h4, hlam, p1665_1, p1798_2]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h0, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1285, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1285, h1659, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h0, h1285, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h4, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h0, h1654, h1659, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    rcases p1798_3 (m.d 0 2) (by simp) with h1818 | h1818
                                    · rcases p1798_3 (m.d 1 2) (by simp) with h1819 | h1819
                                      · linarith only [h1285, h1819, hlam]
                                      · linarith only [h1654, h1819, hlam]
                                    · linarith only [h1818, h5, hlam]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    rcases p1798_3 (m.d 0 2) (by simp) with h1823 | h1823
                                    · rcases p1798_3 (m.d 1 2) (by simp) with h1824 | h1824
                                      · linarith only [h1285, h1824, hlam]
                                      · linarith only [h1655, h1824, hlam]
                                    · linarith only [h1823, h6, hlam]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h5, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1654, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1659, hlam, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1661, hlam, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h6, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1655, hlam, p1798_0]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h1660, hlam, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [h0, h1655, h1659, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                                  · have p1798_0 := h1798c.1
                                    have p1798_1 := h1798c.2.1
                                    have p1798_2 := h1798c.2.2.1
                                    have p1798_3 := h1798c.2.2.2
                                    linarith only [hlam, p1798_0]
                                · linarith only [h1717, h9, hc03, hlam, p1665_1]
                                · linarith only [h1717, hc03, hlam, p1665_1]
                          · linarith only [h1712, h8, hlam]
                        · linarith only [h1711, h6, hlam]
                      · linarith only [h1710, h3, hlam]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h2, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h5, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h7, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h9, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h3, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h6, hlam, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h8, hlam, p1665_0]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [h1654, h1659, h2, h9, hc34, hc45, hlam, hphi, p1665_1]
                    · have p1665_0 := h1665c.1
                      have p1665_1 := h1665c.2.1
                      have p1665_2 := h1665c.2.2.1
                      have p1665_3 := h1665c.2.2.2
                      linarith only [hlam, p1665_0]
              · linarith only [h0, h1285, h1655, h1660, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1285, h1654, h1659, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1285, h1654, h1656, h7, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1856 | h1856
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1857 | h1857
          · linarith only [h1857, h2, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1859 | h1859
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1860 | h1860
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1861 | h1861
                · linarith only [h1654, h1655, h1861, h6, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                  · linarith only [h1654, h1655, h1859, h1863, h6, h9, hlam]
                  · rcases h0bigk with h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h0, h1654, h1859, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h1, h1285, h1654, h1859, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      rcases p1865_3 (m.d 0 1) (by simp) with h1869 | h1869
                      · rcases p1865_3 (m.d 0 2) (by simp) with h1870 | h1870
                        · linarith only [h0, h1870, hlam]
                        · linarith only [h1870, h5, hlam]
                      · linarith only [h1869, h2, hlam]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h1654, h1655, h1859, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h0, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h1654, h1655, h1859, h1860, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      rcases p1865_3 (m.d 0 1) (by simp) with h1878 | h1878
                      · rcases p1865_3 (m.d 0 2) (by simp) with h1879 | h1879
                        · rcases p1865_3 (m.d 0 3) (by simp) with h1880 | h1880
                          · linarith only [h1880, h4, hlam]
                          · linarith only [h1880, h7, hlam]
                        · linarith only [h1879, h5, hlam]
                      · linarith only [h1878, h2, hlam]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h0, h1654, h1655, h1859, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h1, hlam, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h4, hlam, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      rcases p1865_3 (m.d 0 1) (by simp) with h1889 | h1889
                      · rcases p1865_3 (m.d 0 2) (by simp) with h1890 | h1890
                        · rcases p1865_3 (m.d 0 3) (by simp) with h1891 | h1891
                          · rcases p1865_3 (m.d 0 4) (by simp) with h1892 | h1892
                            · linarith only [h1892, h7, hlam]
                            · rcases p1865_3 (m.d 0 5) (by simp) with h1894 | h1894
                              · linarith only [h1894, h8, hlam]
                              · linarith only [h1894, h9, hlam]
                          · linarith only [h1891, h7, hlam]
                        · linarith only [h1890, h5, hlam]
                      · linarith only [h1889, h2, hlam]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h0, h1654, h1655, h1859, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h2, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h5, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h7, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h9, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h3, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h6, hlam, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h8, hlam, p1865_0]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [h9, hc04, hc45, hlam, hphi, p1865_1]
                    · have p1865_0 := h1865c.1
                      have p1865_1 := h1865c.2.1
                      have p1865_2 := h1865c.2.2.1
                      have p1865_3 := h1865c.2.2.2
                      linarith only [hlam, p1865_0]
              · linarith only [h0, h1285, h1654, h1859, h1860, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1285, h1654, h1859, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1285, h1654, h1856, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1914 | h1914
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1915 | h1915
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1916 | h1916
          · linarith only [h1654, h1914, h1916, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1654, h1914, h1916, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1919 | h1919
          · linarith only [h1285, h1914, h1915, h1919, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1654, h1914, h1919, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1922 | h1922
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1923 | h1923
          · linarith only [h1923, h2, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1925 | h1925
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1926 | h1926
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1927 | h1927
                · linarith only [h1927, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1929 | h1929
                  · linarith only [h1654, h1929, h5, h9, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1, h1922, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1654, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1654, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h0, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1654, h5, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h0, h1654, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h0, h1654, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1, hlam, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h4, hlam, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1654, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h0, h1654, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h2, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h5, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h7, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h9, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h3, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h6, hlam, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h8, hlam, p1931_0]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [h1654, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1931_1]
                    · have p1931_0 := h1931c.1
                      have p1931_1 := h1931c.2.1
                      have p1931_2 := h1931c.2.2.1
                      have p1931_3 := h1931c.2.2.2
                      linarith only [hlam, p1931_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1957 | h1957
                · linarith only [h1957, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1959 | h1959
                  · linarith only [h1654, h1925, h1926, h1959, h8, h9, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1, h1922, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1, h1922, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1654, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1654, h1925, h1926, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h0, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1, h1922, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h0, h1654, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h0, h1654, h1925, h1926, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h4, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1654, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h0, h1654, h1925, h1926, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h2, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h5, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h7, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h9, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h3, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h6, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h8, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1654, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
            · linarith only [h1, h1285, h1922, h1925, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1988 | h1988
          · linarith only [h1654, h1988, h5, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1990 | h1990
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1991 | h1991
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1992 | h1992
                · linarith only [h1992, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1994 | h1994
                  · linarith only [h0, h1990, h1994, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1991, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1285, h1922, h1990, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1285, h1922, h1990, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h0, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1285, h1922, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h0, h1285, h1922, h1990, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h0, h1285, h1922, h1990, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1, hlam, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h4, hlam, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1285, h1922, h1990, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h0, h1285, h1922, h1990, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h2, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h5, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h7, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h9, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h3, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h6, hlam, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h8, hlam, p1996_0]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [h1285, h1922, h1990, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1996_1]
                    · have p1996_0 := h1996c.1
                      have p1996_1 := h1996c.2.1
                      have p1996_2 := h1996c.2.2.1
                      have p1996_3 := h1996c.2.2.2
                      linarith only [hlam, p1996_0]
              · linarith only [h1285, h1922, h1990, h1991, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1285, h1990, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
